use std::vec;

use ast::{AstToken, AstNode};
use interner::{Interner, Key};
use la_arena::{Arena, ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::SyntaxTree;
use text_size::TextRange;

use crate::{
    index,
    nameres::{Path, PathWithRange},
    world_index::{WorldIndex, GetDefinitionError},
    Fqn, Index, Name, Definition, Function,
};

#[derive(Clone)]
pub struct Bodies {
    local_defs: Arena<LocalDef>,
    stmts: Arena<Stmt>,
    exprs: Arena<Expr>,
    expr_ranges: ArenaMap<Idx<Expr>, TextRange>,
    function_bodies: FxHashMap<Name, Idx<Expr>>,
    other_module_references: FxHashSet<Fqn>,
    symbol_map: FxHashMap<ast::Ident, Symbol>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Missing,
    IntLiteral(u32),
    StringLiteral(String),
    Binary {
        lhs: Idx<Expr>,
        rhs: Idx<Expr>,
        op: BinaryOp,
    },
    Unary {
        expr: Idx<Expr>,
        op: UnaryOp,
    },
    Block {
        stmts: Vec<Idx<Stmt>>,
    },
    Paren {
        expr: Idx<Expr>,
    },
    Local(Idx<LocalDef>),
    Global(PathWithRange),
    Param {
        idx: u32,
    },
    Call {
        path: PathWithRange,
        args: Vec<Idx<Expr>>,
    },
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Return(Idx<Expr>),
    Expr(Idx<Expr>),
    LocalDef(Idx<LocalDef>),
}

#[derive(Clone)]
pub struct LocalDef {
    pub value: Idx<Expr>,
    pub ast: ast::VarDef,
}

impl std::fmt::Debug for LocalDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LocalDef")
            .field("value", &self.value)
            .finish()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    Pos,
    Neg,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweringDiagnostic {
    pub kind: LoweringDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweringDiagnosticKind {
    OutOfRangeIntLiteral,
    UndefinedLocal { name: Key },
    UndefinedModule { name: Key },
    MismatchedArgCount { name: Key, expected: u32, got: u32 },
    CalledNonLambda { name: Key },
    InvalidEscape,
}

#[derive(Clone, Copy)]
pub enum Symbol {
    Local(Idx<LocalDef>),
    Param(ast::Param),
    Global(Path),
    Function(Path),
    Module(Name),
    Unknown,
}

pub fn lower(
    root: ast::Root,
    tree: &SyntaxTree,
    index: &Index,
    world_index: &WorldIndex,
    interner: &mut Interner,
) -> (Bodies, Vec<LoweringDiagnostic>) {
    let mut ctx = Ctx::new(index, world_index, interner, tree);

    for def in root.defs(tree) {
        match def.value(tree) {
            Some(ast::Expr::Lambda(lambda)) => ctx.lower_lambda(def.name(tree), lambda),
            _ => {}
        }
    }

    ctx.bodies.shrink_to_fit();

    (ctx.bodies, ctx.diagnostics)
}

struct Ctx<'a> {
    bodies: Bodies,
    index: &'a Index,
    world_index: &'a WorldIndex,
    interner: &'a mut Interner,
    tree: &'a SyntaxTree,
    diagnostics: Vec<LoweringDiagnostic>,
    scopes: Vec<FxHashMap<Key, Idx<LocalDef>>>,
    params: FxHashMap<Key, (u32, ast::Param)>,
}

impl<'a> Ctx<'a> {
    fn new(
        index: &'a Index,
        world_index: &'a WorldIndex,
        interner: &'a mut Interner,
        tree: &'a SyntaxTree,
    ) -> Self {
        Self {
            bodies: Bodies {
                local_defs: Arena::new(),
                stmts: Arena::new(),
                exprs: Arena::new(),
                expr_ranges: ArenaMap::default(),
                function_bodies: FxHashMap::default(),
                other_module_references: FxHashSet::default(),
                symbol_map: FxHashMap::default(),
            },
            index,
            world_index,
            interner,
            tree,
            diagnostics: Vec::new(),
            scopes: vec![FxHashMap::default()],
            params: FxHashMap::default(),
        }
    }

    fn lower_lambda(&mut self, name_token: Option<ast::Ident>, lambda: ast::Lambda) {
        let name = match name_token {
            Some(ident) => Name(self.interner.intern(ident.text(self.tree))),
            None => return,
        };

        // if we’ve already seen a function with this name,
        // we ignore all other functions with that name
        //
        // we don’t have to worry about emitting a diagnostic here
        // because indexing already handles this
        if self.bodies.function_bodies.contains_key(&name) {
            return;
        }

        if let Some(param_list) = lambda.param_list(self.tree) {
            for (idx, param) in param_list.params(self.tree).enumerate() {
                if let Some(ident) = param.name(self.tree) {
                    self.params
                        .insert(self.interner.intern(ident.text(self.tree)), (idx as u32, param));
                }
            }
        }

        let body = self.lower_expr(lambda.body(self.tree));
        self.params.clear();
        self.bodies.function_bodies.insert(name, body);
    }

    fn lower_stmt(&mut self, stmt: ast::Stmt) -> Stmt {
        match stmt {
            ast::Stmt::VarDef(local_def) => self.lower_local_def(local_def),
            ast::Stmt::Expr(expr_stmt) => {
                let expr = self.lower_expr(expr_stmt.expr(self.tree));
                Stmt::Expr(expr)
            }
            ast::Stmt::Return(return_stmt) => {
                let expr = self.lower_expr(return_stmt.value(self.tree));
                Stmt::Return(expr)
            },
        }
    }

    fn lower_local_def(&mut self, local_def: ast::VarDef) -> Stmt {
        let value = self.lower_expr(local_def.value(self.tree));
        let id = self.bodies.local_defs.alloc(LocalDef { value, ast: local_def });

        if let Some(ident) = local_def.name(self.tree) {
            let name = self.interner.intern(ident.text(self.tree));
            self.insert_into_current_scope(name, id);
        }

        Stmt::LocalDef(id)
    }

    fn lower_expr(&mut self, expr: Option<ast::Expr>) -> Idx<Expr> {
        let expr_ast = match expr {
            Some(expr) => expr,
            None => return self.bodies.exprs.alloc(Expr::Missing),
        };

        let range = expr_ast.range(self.tree);

        let expr = match expr_ast {
            ast::Expr::Binary(binary_expr) => self.lower_binary_expr(binary_expr),
            ast::Expr::Unary(unary_expr) => self.lower_unary_expr(unary_expr),
            ast::Expr::Block(block) => self.lower_block(block),
            ast::Expr::Paren(paren) => self.lower_paren_expr(paren),
            ast::Expr::Call(call) => self.lower_call(call),
            ast::Expr::Ref(var_ref) => self.lower_ref(var_ref),
            ast::Expr::IntLiteral(int_literal) => self.lower_int_literal(int_literal),
            ast::Expr::StringLiteral(string_literal) => self.lower_string_literal(string_literal),
            ast::Expr::Lambda(_) => unreachable!(),
        };

        let id = self.bodies.exprs.alloc(expr);
        self.bodies.expr_ranges.insert(id, range);

        id
    }

    fn lower_binary_expr(&mut self, binary_expr: ast::BinaryExpr) -> Expr {
        let lhs = self.lower_expr(binary_expr.lhs(self.tree));
        let rhs = self.lower_expr(binary_expr.rhs(self.tree));

        let op = match binary_expr.op(self.tree) {
            Some(ast::BinaryOp::Add(_)) => BinaryOp::Add,
            Some(ast::BinaryOp::Sub(_)) => BinaryOp::Sub,
            Some(ast::BinaryOp::Mul(_)) => BinaryOp::Mul,
            Some(ast::BinaryOp::Div(_)) => BinaryOp::Div,
            None => return Expr::Missing,
        };

        Expr::Binary { lhs, rhs, op }
    }

    fn lower_unary_expr(&mut self, unary_expr: ast::UnaryExpr) -> Expr {
        let expr = self.lower_expr(unary_expr.expr(self.tree));

        let op = match unary_expr.op(self.tree) {
            Some(ast::UnaryOp::Pos(_)) => UnaryOp::Pos,
            Some(ast::UnaryOp::Neg(_)) => UnaryOp::Neg,
            None => return Expr::Missing,
        };

        Expr::Unary { expr, op }
    }

    fn lower_block(&mut self, block: ast::Block) -> Expr {
        self.create_new_child_scope();

        let mut stmts = Vec::new();

        for stmt in block.stmts(self.tree) {
            let statement = self.lower_stmt(stmt);
            stmts.push(self.bodies.stmts.alloc(statement));
        }

        // let tail_expr =
        //     block.tail_expr(self.tree).map(|tail_expr| self.lower_expr(Some(tail_expr)));

        self.destroy_current_scope();

        Expr::Block { stmts }
    }

    fn lower_paren_expr(&mut self, paren: ast::ParenExpr) -> Expr {
        Expr::Paren { expr: self.lower_expr(paren.expr(self.tree)) }
    }

    fn lower_call(&mut self, call: ast::Call) -> Expr {
        let path = match call.name(self.tree) {
            Some(path) => path,
            None => return Expr::Missing,
        };

        let ident = match path.top_level_name(self.tree) {
            Some(ident) => ident,
            None => return Expr::Missing,
        };

        if let Some(function_name_token) = path.nested_name(self.tree) {
            let module_name_token = ident;

            let module_name = self.interner.intern(module_name_token.text(self.tree));
            let function_name = self.interner.intern(function_name_token.text(self.tree));

            let fqn = Fqn { module: Name(module_name), name: Name(function_name) };

            match self.world_index.get_definition(fqn) {
                Ok(definition) => {
                    let path = PathWithRange::OtherModule {
                        fqn,
                        module_range: module_name_token.range(self.tree),
                        name_range: function_name_token.range(self.tree),
                    };

                    self.bodies.other_module_references.insert(fqn);

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Module(Name(module_name)));

                    match definition {
                        Definition::Function(function) => {
                            self.bodies
                                .symbol_map
                                .insert(function_name_token, Symbol::Function(path.path()));
                            return lower(self, call, function, path, function_name_token);
                        }
                        Definition::Global(_) => todo!(),
                    }
                },
                Err(GetDefinitionError::UnknownModule) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::UndefinedModule { name: module_name },
                        range: module_name_token.range(self.tree),
                    });

                    self.bodies.symbol_map.insert(module_name_token, Symbol::Unknown);
                    self.bodies.symbol_map.insert(function_name_token, Symbol::Unknown);

                    return Expr::Missing;
                },
                Err(GetDefinitionError::UnknownDefinition) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::UndefinedLocal { name: function_name },
                        range: function_name_token.range(self.tree),
                    });

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Module(Name(module_name)));
                    self.bodies.symbol_map.insert(function_name_token, Symbol::Unknown);

                    return Expr::Missing;
                }
            }
        }

        // only have one ident as path
        let name = self.interner.intern(ident.text(self.tree));

        if let Some(def) = self.look_up_in_current_scope(name) {
            self.diagnostics.push(LoweringDiagnostic {
                kind: LoweringDiagnosticKind::CalledNonLambda { name },
                range: ident.range(self.tree),
            });

            self.bodies.symbol_map.insert(ident, Symbol::Local(def));
            return Expr::Local(def);
        }

        // todo: allow calling parameters
        if let Some((idx, ast)) = self.look_up_param(name) {
            self.diagnostics.push(LoweringDiagnostic {
                kind: LoweringDiagnosticKind::CalledNonLambda { name },
                range: ident.range(self.tree),
            });

            self.bodies.symbol_map.insert(ident, Symbol::Param(ast));
            return Expr::Param { idx };
        }

        let name = Name(name);
        if let Some(definition) = self.index.get_definition(name) {
            let path = PathWithRange::ThisModule { name, range: ident.range(self.tree) };

            match definition {
                Definition::Function(function) => {
                    self.bodies.symbol_map.insert(ident, Symbol::Function(path.path()));
                    return lower(self, call, function, path, ident);
                }
                _ => todo!(),
            }
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::UndefinedLocal { name: name.0 },
            range: ident.range(self.tree),
        });

        self.bodies.symbol_map.insert(ident, Symbol::Unknown);

        fn lower(
            ctx: &mut Ctx,
            call: ast::Call,
            function: &Function,
            path: PathWithRange,
            ident: ast::Ident,
        ) -> Expr {
            let arg_list = call.arg_list(ctx.tree);
    
            let expected = function.params.len() as u32;
            let got = match &arg_list {
                Some(al) => al.args(ctx.tree).count() as u32,
                None => 0,
            };
    
            if expected != got {
                let name = match path {
                    PathWithRange::ThisModule { name, .. } => name.0,
                    PathWithRange::OtherModule { fqn, .. } => fqn.name.0,
                };
    
                ctx.diagnostics.push(LoweringDiagnostic {
                    kind: LoweringDiagnosticKind::MismatchedArgCount { name, expected, got },
                    range: ident.range(ctx.tree),
                });
    
                return Expr::Missing;
            }
    
            let mut args = Vec::new();
    
            if let Some(arg_list) = arg_list {
                for arg in arg_list.args(ctx.tree) {
                    let expr = ctx.lower_expr(arg.value(ctx.tree));
                    args.push(expr);
                }
            }
    
            Expr::Call { path, args }
        }

        return Expr::Missing;
    }


    fn lower_ref(&mut self, var_ref: ast::Ref) -> Expr {
        let path = match var_ref.name(self.tree) {
            Some(path) => path,
            None => return Expr::Missing,
        };

        let ident = match path.top_level_name(self.tree) {
            Some(ident) => ident,
            None => return Expr::Missing,
        };

        if let Some(var_name_token) = path.nested_name(self.tree) {
            let module_name_token = ident;

            let module_name = self.interner.intern(module_name_token.text(self.tree));
            let var_name = self.interner.intern(var_name_token.text(self.tree));

            let fqn = Fqn { module: Name(module_name), name: Name(var_name) };

            match self.world_index.get_definition(fqn) {
                Ok(definition) => {
                    let path = PathWithRange::OtherModule {
                        fqn,
                        module_range: module_name_token.range(self.tree),
                        name_range: var_name_token.range(self.tree),
                    };

                    self.bodies.other_module_references.insert(fqn);

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Module(Name(module_name)));

                    self.bodies
                        .symbol_map
                        .insert(var_name_token, Symbol::Global(path.path()));

                    return Expr::Global(path);
                },
                Err(GetDefinitionError::UnknownModule) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::UndefinedModule { name: module_name },
                        range: module_name_token.range(self.tree),
                    });

                    self.bodies.symbol_map.insert(module_name_token, Symbol::Unknown);
                    self.bodies.symbol_map.insert(var_name_token, Symbol::Unknown);

                    return Expr::Missing;
                },
                Err(GetDefinitionError::UnknownDefinition) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::UndefinedLocal { name: var_name },
                        range: var_name_token.range(self.tree),
                    });

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Module(Name(module_name)));
                    self.bodies.symbol_map.insert(var_name_token, Symbol::Unknown);

                    return Expr::Missing;
                }
            }
        }

        // only have one ident as path
        let name = self.interner.intern(ident.text(self.tree));

        if let Some(def) = self.look_up_in_current_scope(name) {
            self.bodies.symbol_map.insert(ident, Symbol::Local(def));
            return Expr::Local(def);
        }

        if let Some((idx, ast)) = self.look_up_param(name) {
            self.bodies.symbol_map.insert(ident, Symbol::Param(ast));
            return Expr::Param { idx };
        }

        let name = Name(name);
        if let Some(definition) = self.index.get_definition(name) {
            let path = PathWithRange::ThisModule { name, range: ident.range(self.tree) };

            self.bodies.symbol_map.insert(ident, Symbol::Global(path.path()));
            
            return Expr::Global(path);
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::UndefinedLocal { name: name.0 },
            range: ident.range(self.tree),
        });

        self.bodies.symbol_map.insert(ident, Symbol::Unknown);

        return Expr::Missing;
    }

    fn lower_int_literal(&mut self, int_literal: ast::IntLiteral) -> Expr {
        let value = int_literal.value(self.tree).and_then(|int| int.text(self.tree).parse().ok());

        if let Some(value) = value {
            return Expr::IntLiteral(value);
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::OutOfRangeIntLiteral,
            range: int_literal.range(self.tree),
        });

        Expr::Missing
    }

    fn lower_string_literal(&mut self, string_literal: ast::StringLiteral) -> Expr {
        let mut text = String::new();

        for component in string_literal.components(self.tree) {
            match component {
                ast::StringComponent::Escape(escape) => {
                    let escape_text = escape.text(self.tree);
                    let mut chars = escape_text.chars();
                    if cfg!(debug_assertions) {
                        assert_eq!(chars.next(), Some('\\'));
                    } else {
                        chars.next();
                    }

                    let escape_char = chars.next().unwrap();
                    debug_assert!(chars.next().is_none());

                    match escape_char {
                        '"' => text.push('"'),
                        '\\' => text.push('\\'),
                        'n' => text.push('\n'),
                        'r' => text.push('\r'),
                        't' => text.push('\t'),
                        _ => self.diagnostics.push(LoweringDiagnostic {
                            kind: LoweringDiagnosticKind::InvalidEscape,
                            range: escape.range(self.tree),
                        }),
                    }
                }
                ast::StringComponent::Contents(contents) => {
                    text.push_str(contents.text(self.tree));
                }
            }
        }

        Expr::StringLiteral(text)
    }

    fn insert_into_current_scope(&mut self, name: Key, id: Idx<LocalDef>) {
        self.scopes.last_mut().unwrap().insert(name, id);
    }
    
    fn look_up_in_current_scope(&mut self, name: Key) -> Option<Idx<LocalDef>> {
        for scope in self.scopes.iter().rev() {
            if let Some(def) = scope.get(&name) {
                return Some(*def);
            }
        }

        None
    }

    fn look_up_param(&mut self, name: Key) -> Option<(u32, ast::Param)> {
        self.params.get(&name).copied()
    }

    fn create_new_child_scope(&mut self) {
        self.scopes.push(FxHashMap::default());
    }
    
    fn destroy_current_scope(&mut self) {
        self.scopes.pop();
    }
}

impl Bodies {
    pub fn function_body(&self, name: Name) -> Idx<Expr> {
        self.function_bodies[&name]
    }

    pub fn range_for_expr(&self, expr: Idx<Expr>) -> TextRange {
        self.expr_ranges[expr]
    }

    pub fn other_module_references(&self) -> &FxHashSet<Fqn> {
        &self.other_module_references
    }

    pub fn symbol(&self, ident: ast::Ident) -> Option<Symbol> {
        self.symbol_map.get(&ident).copied()
    }

    fn shrink_to_fit(&mut self) {
        let Self {
            local_defs,
            stmts,
            exprs,
            expr_ranges,
            function_bodies,
            other_module_references,
            symbol_map,
        } = self;

        local_defs.shrink_to_fit();
        stmts.shrink_to_fit();
        exprs.shrink_to_fit();
        //expr_ranges.shrink_to_fit();
        function_bodies.shrink_to_fit();
        other_module_references.shrink_to_fit();
        symbol_map.shrink_to_fit();
    }
}

impl std::ops::Index<Idx<LocalDef>> for Bodies {
    type Output = LocalDef;

    fn index(&self, id: Idx<LocalDef>) -> &Self::Output {
        &self.local_defs[id]
    }
}

impl std::ops::Index<Idx<Stmt>> for Bodies {
    type Output = Stmt;

    fn index(&self, id: Idx<Stmt>) -> &Self::Output {
        &self.stmts[id]
    }
}

impl std::ops::Index<Idx<Expr>> for Bodies {
    type Output = Expr;

    fn index(&self, id: Idx<Expr>) -> &Self::Output {
        &self.exprs[id]
    }
}

impl Bodies {
    pub fn debug(&self, interner: &Interner) -> String {
        let mut s = String::new();

        let mut function_bodies: Vec<_> = self.function_bodies.iter().collect();
        function_bodies.sort_unstable_by_key(|(name, _)| *name);

        for (name, expr_id) in function_bodies {
            s.push_str(&format!("{} = () -> _ ", interner.lookup(name.0)));
            write_expr(*expr_id, self, &mut s, interner, 0);
            s.push_str(";\n");
        }

        if !self.other_module_references.is_empty() {
            let mut other_module_references: Vec<_> = self.other_module_references.iter().collect();
            other_module_references.sort_unstable();

            s.push_str("\nReferences to other modules:\n");
            for fqn in &other_module_references {
                s.push_str(&format!(
                    "- {}.{}\n",
                    interner.lookup(fqn.module.0),
                    interner.lookup(fqn.name.0)
                ));
            }
        }

        return s;

        fn write_expr(
            id: Idx<Expr>,
            bodies: &Bodies,
            s: &mut String,
            interner: &Interner,
            mut indentation: usize,
        ) {
            match &bodies[id] {
                Expr::Missing => s.push_str("<missing>"),

                Expr::IntLiteral(n) => s.push_str(&format!("{}", n)),

                Expr::StringLiteral(content) => s.push_str(&format!("{content:?}")),

                Expr::Binary { lhs, rhs, op } => {
                    write_expr(*lhs, bodies, s, interner, indentation);

                    s.push(' ');

                    match op {
                        BinaryOp::Add => s.push('+'),
                        BinaryOp::Sub => s.push('-'),
                        BinaryOp::Mul => s.push('*'),
                        BinaryOp::Div => s.push('/'),
                    }

                    s.push(' ');

                    write_expr(*rhs, bodies, s, interner, indentation);
                }

                Expr::Unary { expr, op } => {

                    s.push(' ');

                    match op {
                        UnaryOp::Pos => s.push('+'),
                        UnaryOp::Neg => s.push('-'),
                    }

                    write_expr(*expr, bodies, s, interner, indentation);
                }

                Expr::Block { stmts } if stmts.is_empty() => {
                    s.push_str("{}");
                }

                Expr::Block { stmts } => {
                    indentation += 4;

                    s.push_str("{\n");

                    for stmt in stmts.clone() {
                        s.push_str(&" ".repeat(indentation));
                        write_stmt(stmt, bodies, s, interner, indentation);
                        s.push('\n');
                    }

                    indentation -= 4;
                    s.push_str(&" ".repeat(indentation));

                    s.push('}');
                }

                Expr::Paren { expr } => {
                    s.push_str("(");
                    write_expr(*expr, bodies, s, interner, indentation);
                    s.push(')');
                }

                Expr::Local(id) => s.push_str(&format!("l{}", id.into_raw())),

                Expr::Param { idx } => s.push_str(&format!("p{}", idx)),

                Expr::Call { path, args } => {
                    match path {
                        PathWithRange::ThisModule { name, .. } => {
                            s.push_str(interner.lookup(name.0))
                        }
                        PathWithRange::OtherModule { fqn, .. } => s.push_str(&format!(
                            "{}.{}",
                            interner.lookup(fqn.module.0),
                            interner.lookup(fqn.name.0)
                        )),
                    }

                    s.push_str("(");
                    for (idx, arg) in args.iter().enumerate() {
                        if idx == 0 {
                            s.push(' ');
                        } else {
                            s.push_str(", ");
                        }

                        write_expr(*arg, bodies, s, interner, indentation);
                    }
                    s.push_str(")");
                }

                Expr::Global(path) => {
                    match path {
                        PathWithRange::ThisModule { name, .. } => {
                            s.push_str(interner.lookup(name.0))
                        }
                        PathWithRange::OtherModule { fqn, .. } => s.push_str(&format!(
                            "{}.{}",
                            interner.lookup(fqn.module.0),
                            interner.lookup(fqn.name.0)
                        )),
                    }
                }
            }
        }

        fn write_stmt(
            id: Idx<Stmt>,
            bodies: &Bodies,
            s: &mut String,
            interner: &Interner,
            indentation: usize,
        ) {
            match &bodies[id] {
                Stmt::Expr(expr_id) => {
                    write_expr(*expr_id, bodies, s, interner, indentation);
                    s.push(';');
                }
                Stmt::LocalDef(local_def_id) => {
                    s.push_str(&format!("let l{} = ", local_def_id.into_raw()));
                    write_expr(bodies[*local_def_id].value, bodies, s, interner, indentation);
                    s.push(';');
                }
                Stmt::Return(return_expr) => {
                    s.push_str("return ");
                    write_expr(*return_expr, bodies, s, interner, indentation);
                    s.push(';');
                },
            }
        }
    }
}
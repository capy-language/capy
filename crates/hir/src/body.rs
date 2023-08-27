use std::vec;

use ast::{AstNode, AstToken};
use interner::{Interner, Key};
use la_arena::{Arena, ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::SyntaxTree;
use text_size::TextRange;

use crate::{
    nameres::{Path, PathWithRange},
    world_index::{GetDefinitionError, WorldIndex},
    Definition, Fqn, Function, Name, Param, TyParseError, TyWithRange, UIDGenerator,
};

#[derive(Clone)]
pub struct Bodies {
    local_defs: Arena<LocalDef>,
    assigns: Arena<Assign>,
    stmts: Arena<Stmt>,
    exprs: Arena<Expr>,
    expr_ranges: ArenaMap<Idx<Expr>, TextRange>,
    function_bodies: FxHashMap<Name, Idx<Expr>>,
    globals: FxHashMap<Name, Idx<Expr>>,
    lambdas: Arena<Lambda>,
    other_module_references: FxHashSet<Fqn>,
    symbol_map: FxHashMap<ast::Ident, Symbol>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Missing,
    IntLiteral(u64),
    FloatLiteral(f64),
    BoolLiteral(bool),
    StringLiteral(String),
    Cast {
        expr: Idx<Expr>,
        ty: Idx<TyWithRange>,
    },
    Ref {
        mutable: bool,
        expr: Idx<Expr>,
    },
    Deref {
        pointer: Idx<Expr>,
    },
    Binary {
        lhs: Idx<Expr>,
        rhs: Idx<Expr>,
        op: BinaryOp,
    },
    Unary {
        expr: Idx<Expr>,
        op: UnaryOp,
    },
    Array {
        size: Option<u64>,
        items: Vec<Idx<Expr>>,
        ty: Idx<TyWithRange>,
    },
    Index {
        array: Idx<Expr>,
        index: Idx<Expr>,
    },
    Block {
        stmts: Vec<Idx<Stmt>>,
        tail_expr: Option<Idx<Expr>>,
    },
    If {
        condition: Idx<Expr>,
        body: Idx<Expr>,
        else_branch: Option<Idx<Expr>>,
    },
    While {
        condition: Option<Idx<Expr>>,
        body: Idx<Expr>,
    },
    Local(Idx<LocalDef>),
    Global(PathWithRange),
    Param {
        idx: u32,
    },
    Call {
        callee: Idx<Expr>,
        args: Vec<Idx<Expr>>,
    },
    Lambda(Idx<Lambda>),
    /// either a primitive type (such as `i32`, `bool`, etc.), or an array type,
    /// or a pointer to a primitive type, or a distinct type
    PrimitiveTy {
        ty: Idx<TyWithRange>,
    },
}

#[derive(Debug, Clone)]
pub struct Lambda {
    pub function: Function,
    pub body: Idx<Expr>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Idx<Expr>),
    LocalDef(Idx<LocalDef>),
    Assign(Idx<Assign>),
}

#[derive(Clone)]
pub struct LocalDef {
    pub mutable: bool,
    pub ty: Idx<Expr>,
    pub value: Idx<Expr>,
    pub ast: ast::Define,
    pub range: TextRange,
}

#[derive(Clone)]
pub struct Assign {
    pub source: Idx<Expr>,
    pub value: Idx<Expr>,
    pub range: TextRange,
    pub ast: ast::Assign,
}

impl std::fmt::Debug for LocalDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LocalDef")
            .field("value", &self.value)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOp {
    // math operations
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // cmp operations
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,

    // boolean operations
    And,
    Or,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    // math operations
    Pos,
    Neg,

    // boolean operations
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweringDiagnostic {
    pub kind: LoweringDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweringDiagnosticKind {
    OutOfRangeIntLiteral,
    OutOfRangeFloatLiteral,
    UndefinedLocal { name: Key },
    UndefinedModule { name: Key },
    NonGlobalExtern,
    ArraySizeMismatch { found: u32, expected: u32 },
    TyParseError(TyParseError),
    InvalidEscape,
}

#[derive(Clone, Copy)]
pub enum Symbol {
    Local(Idx<LocalDef>),
    Param(ast::Param),
    Global(Path),
    PrimitiveTy(Idx<TyWithRange>),
    Function(Path),
    Module(Name),
    Unknown,
}

pub fn lower(
    root: ast::Root,
    tree: &SyntaxTree,
    module: Name,
    world_index: &WorldIndex,
    uid_gen: &mut UIDGenerator,
    twr_arena: &mut Arena<TyWithRange>,
    interner: &mut Interner,
) -> (Bodies, Vec<LoweringDiagnostic>) {
    let mut ctx = Ctx::new(module, world_index, uid_gen, twr_arena, interner, tree);

    for def in root.defs(tree) {
        let (name, value) = match def {
            ast::Define::Binding(binding) => (binding.name(tree), binding.value(tree)),
            ast::Define::Variable(variable) => (variable.name(tree), variable.value(tree)),
        };
        match value {
            Some(ast::Expr::Lambda(lambda)) => ctx.lower_function(name, lambda),
            val => ctx.lower_global(name, val),
        }
    }

    ctx.bodies.shrink_to_fit();

    (ctx.bodies, ctx.diagnostics)
}

struct Ctx<'a> {
    bodies: Bodies,
    module: Name,
    world_index: &'a WorldIndex,
    uid_gen: &'a mut UIDGenerator,
    twr_arena: &'a mut Arena<TyWithRange>,
    interner: &'a mut Interner,
    tree: &'a SyntaxTree,
    diagnostics: Vec<LoweringDiagnostic>,
    scopes: Vec<FxHashMap<Key, Idx<LocalDef>>>,
    params: FxHashMap<Key, (u32, ast::Param)>,
}

impl<'a> Ctx<'a> {
    fn new(
        module: Name,
        world_index: &'a WorldIndex,
        uid_gen: &'a mut UIDGenerator,
        twr_arena: &'a mut Arena<TyWithRange>,
        interner: &'a mut Interner,
        tree: &'a SyntaxTree,
    ) -> Self {
        Self {
            bodies: Bodies {
                local_defs: Arena::new(),
                assigns: Arena::new(),
                stmts: Arena::new(),
                exprs: Arena::new(),
                expr_ranges: ArenaMap::default(),
                function_bodies: FxHashMap::default(),
                globals: FxHashMap::default(),
                lambdas: Arena::new(),
                other_module_references: FxHashSet::default(),
                symbol_map: FxHashMap::default(),
            },
            module,
            world_index,
            uid_gen,
            twr_arena,
            interner,
            tree,
            diagnostics: Vec::new(),
            scopes: vec![FxHashMap::default()],
            params: FxHashMap::default(),
        }
    }

    fn lower_ty(&mut self, ty: Option<ast::Ty>) -> TyWithRange {
        match TyWithRange::parse(
            ty.and_then(|ty| ty.expr(self.tree)),
            self.uid_gen,
            self.twr_arena,
            self.interner,
            self.tree,
            false,
        ) {
            Ok(ty) => ty,
            Err((why, range)) => {
                self.diagnostics.push(LoweringDiagnostic {
                    kind: LoweringDiagnosticKind::TyParseError(why),
                    range,
                });

                TyWithRange::Unknown
            }
        }
    }

    fn lower_global(&mut self, name_token: Option<ast::Ident>, expr: Option<ast::Expr>) {
        let name = match name_token {
            Some(ident) => Name(self.interner.intern(ident.text(self.tree))),
            None => return,
        };

        // if we’ve already seen a global with this name,
        // we ignore all other globals with that name
        //
        // we don’t have to worry about emitting a diagnostic here
        // because indexing already handles this
        if self.bodies.globals.contains_key(&name) {
            return;
        }

        let body = self.lower_expr(expr);
        self.bodies.globals.insert(name, body);
    }

    fn lower_function(&mut self, name_token: Option<ast::Ident>, lambda: ast::Lambda) {
        let name = match name_token {
            Some(ident) => Name(self.interner.intern(ident.text(self.tree))),
            None => return,
        };

        // if this is an external function, there are no expr's to lower
        if lambda.r#extern(self.tree).is_some() {
            return;
        }

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
                    self.params.insert(
                        self.interner.intern(ident.text(self.tree)),
                        (idx as u32, param),
                    );
                }
            }
        }

        let body = self.lower_expr(lambda.body(self.tree));
        self.params.clear();
        self.bodies.function_bodies.insert(name, body);
    }

    fn lower_lambda(&mut self, lambda: ast::Lambda) -> Expr {
        let mut params = Vec::new();
        let mut param_type_ranges = Vec::new();

        let old_params = self.params.clone();
        self.params.clear();

        if let Some(param_list) = lambda.param_list(self.tree) {
            for (idx, param) in param_list.params(self.tree).enumerate() {
                let key = param
                    .name(self.tree)
                    .map(|name| self.interner.intern(name.text(self.tree)));

                let ty = param.ty(self.tree);
                param_type_ranges.push(ty.map(|type_| type_.range(self.tree)));

                let ty = self.lower_ty(ty);

                params.push(Param {
                    name: key.map(Name),
                    ty: self.twr_arena.alloc(ty),
                });

                if let Some(key) = key {
                    self.params.insert(key, (idx as u32, param));
                }
            }
        }

        if let Some(r#extern) = lambda.r#extern(self.tree) {
            self.diagnostics.push(LoweringDiagnostic {
                kind: LoweringDiagnosticKind::NonGlobalExtern,
                range: r#extern.range(self.tree),
            });
        }

        let body = self.lower_expr(lambda.body(self.tree));
        self.params = old_params;

        let return_ty = lambda
            .return_ty(self.tree)
            .map_or(TyWithRange::Void { range: None }, |ty| {
                self.lower_ty(Some(ty))
            });

        Expr::Lambda(self.bodies.lambdas.alloc(Lambda {
            function: Function {
                params,
                return_ty: self.twr_arena.alloc(return_ty),
                ty_annotation: self.twr_arena.alloc(TyWithRange::Unknown),
                full_range: lambda.range(self.tree),
                is_extern: lambda.r#extern(self.tree).is_some(), // this doesn't matter since lambdas can't be extern
            },
            body,
        }))
    }

    fn lower_stmt(&mut self, stmt: ast::Stmt) -> Stmt {
        match stmt {
            ast::Stmt::Define(local_def) => self.lower_local_define(local_def),
            ast::Stmt::Assign(local_set) => self.lower_assignment(local_set),
            ast::Stmt::Expr(expr_stmt) => {
                let expr = self.lower_expr(expr_stmt.expr(self.tree));
                Stmt::Expr(expr)
            }
        }
    }

    fn lower_local_define(&mut self, local_def: ast::Define) -> Stmt {
        let ty = self.lower_expr(local_def.ty(self.tree).and_then(|ty| ty.expr(self.tree)));
        let value = self.lower_expr(local_def.value(self.tree));
        let id = self.bodies.local_defs.alloc(LocalDef {
            mutable: matches!(local_def, ast::Define::Variable(_)),
            ty,
            value,
            ast: local_def,
            range: local_def.range(self.tree),
        });

        if let Some(ident) = local_def.name(self.tree) {
            let name = self.interner.intern(ident.text(self.tree));
            self.insert_into_current_scope(name, id);
        }

        Stmt::LocalDef(id)
    }

    fn lower_assignment(&mut self, assign: ast::Assign) -> Stmt {
        let source = self.lower_expr(assign.source(self.tree).unwrap().value(self.tree));
        let value = self.lower_expr(assign.value(self.tree));

        let id = self.bodies.assigns.alloc(Assign {
            source,
            value,
            range: assign.range(self.tree),
            ast: assign,
        });

        Stmt::Assign(id)
    }

    fn lower_expr(&mut self, expr: Option<ast::Expr>) -> Idx<Expr> {
        let expr_ast = match expr {
            Some(expr) => expr,
            None => return self.bodies.exprs.alloc(Expr::Missing),
        };

        let range = expr_ast.range(self.tree);

        let expr = self.lower_expr_raw(expr_ast);

        let id = self.bodies.exprs.alloc(expr);
        self.bodies.expr_ranges.insert(id, range);

        id
    }

    fn lower_expr_raw(&mut self, expr: ast::Expr) -> Expr {
        match expr {
            ast::Expr::Cast(cast_expr) => self.lower_cast_expr(cast_expr),
            ast::Expr::Ref(ref_expr) => self.lower_ref_expr(ref_expr),
            ast::Expr::Deref(deref_expr) => self.lower_deref_expr(deref_expr),
            ast::Expr::Binary(binary_expr) => self.lower_binary_expr(binary_expr),
            ast::Expr::Unary(unary_expr) => self.lower_unary_expr(unary_expr),
            ast::Expr::Array(array_expr) => self.lower_array_expr(array_expr),
            ast::Expr::Block(block) => self.lower_block(block),
            ast::Expr::If(if_expr) => self.lower_if(if_expr),
            ast::Expr::While(while_expr) => self.lower_while(while_expr),
            ast::Expr::Call(call) => self.lower_call(call),
            ast::Expr::IndexExpr(index_expr) => self.lower_index_expr(index_expr),
            ast::Expr::VarRef(var_ref) => self.lower_var_ref(var_ref),
            ast::Expr::IntLiteral(int_literal) => self.lower_int_literal(int_literal),
            ast::Expr::FloatLiteral(float_literal) => self.lower_float_literal(float_literal),
            ast::Expr::BoolLiteral(bool_literal) => self.lower_bool_literal(bool_literal),
            ast::Expr::StringLiteral(string_literal) => self.lower_string_literal(string_literal),
            ast::Expr::Distinct(distinct) => self.lower_distinct(distinct),
            ast::Expr::Lambda(lambda) => self.lower_lambda(lambda),
        }
    }

    fn lower_cast_expr(&mut self, cast_expr: ast::CastExpr) -> Expr {
        let ty = self.lower_ty(cast_expr.ty(self.tree));

        let expr = self.lower_expr(cast_expr.expr(self.tree));

        Expr::Cast {
            expr,
            ty: self.twr_arena.alloc(ty),
        }
    }

    fn lower_ref_expr(&mut self, ref_expr: ast::RefExpr) -> Expr {
        match TyWithRange::parse(
            ref_expr.expr(self.tree),
            self.uid_gen,
            self.twr_arena,
            self.interner,
            self.tree,
            true,
        ) {
            Ok(sub_ty) => {
                return Expr::PrimitiveTy {
                    ty: {
                        let sub_ty = self.twr_arena.alloc(sub_ty);
                        self.twr_arena.alloc(TyWithRange::Pointer {
                            mutable: ref_expr.mutable(self.tree).is_some(),
                            sub_ty,
                            range: ref_expr.range(self.tree),
                        })
                    },
                }
            }
            Err((
                TyParseError::NonPrimitive | TyParseError::NotATy | TyParseError::ArrayHasBody,
                _,
            )) => {}
            Err((why, range)) => {
                self.diagnostics.push(LoweringDiagnostic {
                    kind: LoweringDiagnosticKind::TyParseError(why),
                    range,
                });
                return Expr::PrimitiveTy {
                    ty: self.twr_arena.alloc(TyWithRange::Unknown),
                };
            }
        }

        let expr = self.lower_expr(ref_expr.expr(self.tree));

        Expr::Ref {
            mutable: ref_expr.mutable(self.tree).is_some(),
            expr,
        }
    }

    fn lower_deref_expr(&mut self, deref_expr: ast::DerefExpr) -> Expr {
        let pointer = self.lower_expr(deref_expr.pointer(self.tree));

        Expr::Deref { pointer }
    }

    fn lower_distinct(&mut self, distinct: ast::Distinct) -> Expr {
        let ty = match TyWithRange::parse(
            Some(ast::Expr::Distinct(distinct)),
            self.uid_gen,
            self.twr_arena,
            self.interner,
            self.tree,
            false,
        ) {
            Ok(ty) => ty,
            Err((why, range)) => {
                self.diagnostics.push(LoweringDiagnostic {
                    kind: LoweringDiagnosticKind::TyParseError(why),
                    range,
                });

                TyWithRange::Unknown
            }
        };

        Expr::PrimitiveTy {
            ty: self.twr_arena.alloc(ty),
        }
    }

    fn lower_binary_expr(&mut self, binary_expr: ast::BinaryExpr) -> Expr {
        let lhs = self.lower_expr(binary_expr.lhs(self.tree));
        let rhs = self.lower_expr(binary_expr.rhs(self.tree));

        let op = match binary_expr.op(self.tree) {
            Some(ast::BinaryOp::Add(_)) => BinaryOp::Add,
            Some(ast::BinaryOp::Sub(_)) => BinaryOp::Sub,
            Some(ast::BinaryOp::Mul(_)) => BinaryOp::Mul,
            Some(ast::BinaryOp::Div(_)) => BinaryOp::Div,
            Some(ast::BinaryOp::Mod(_)) => BinaryOp::Mod,
            Some(ast::BinaryOp::Lt(_)) => BinaryOp::Lt,
            Some(ast::BinaryOp::Gt(_)) => BinaryOp::Gt,
            Some(ast::BinaryOp::Le(_)) => BinaryOp::Le,
            Some(ast::BinaryOp::Ge(_)) => BinaryOp::Ge,
            Some(ast::BinaryOp::Eq(_)) => BinaryOp::Eq,
            Some(ast::BinaryOp::Ne(_)) => BinaryOp::Ne,
            Some(ast::BinaryOp::And(_)) => BinaryOp::And,
            Some(ast::BinaryOp::Or(_)) => BinaryOp::Or,
            None => return Expr::Missing,
        };

        Expr::Binary { lhs, rhs, op }
    }

    fn lower_unary_expr(&mut self, unary_expr: ast::UnaryExpr) -> Expr {
        let expr = self.lower_expr(unary_expr.expr(self.tree));

        let op = match unary_expr.op(self.tree) {
            Some(ast::UnaryOp::Pos(_)) => UnaryOp::Pos,
            Some(ast::UnaryOp::Neg(_)) => UnaryOp::Neg,
            Some(ast::UnaryOp::Not(_)) => UnaryOp::Not,
            None => return Expr::Missing,
        };

        Expr::Unary { expr, op }
    }

    fn lower_array_expr(&mut self, array_expr: ast::Array) -> Expr {
        let items = match array_expr.body(self.tree) {
            Some(body) => body
                .items(self.tree)
                .map(|item| self.lower_expr(item.value(self.tree)))
                .collect::<Vec<_>>(),
            None => {
                // if the array doesn't have a body, parse it as a type

                let ty = match TyWithRange::parse(
                    Some(ast::Expr::Array(array_expr)),
                    self.uid_gen,
                    self.twr_arena,
                    self.interner,
                    self.tree,
                    false,
                ) {
                    Ok(ty) => ty,
                    Err((why, range)) => {
                        self.diagnostics.push(LoweringDiagnostic {
                            kind: LoweringDiagnosticKind::TyParseError(why),
                            range,
                        });

                        return Expr::Missing;
                    }
                };

                return Expr::PrimitiveTy {
                    ty: self.twr_arena.alloc(ty),
                };
            }
        };

        let ty = self.lower_ty(array_expr.ty(self.tree));

        let size = array_expr
            .size(self.tree)
            .and_then(|size| size.size(self.tree))
            .map(|size| self.lower_expr_raw(size))
            .and_then(|size| match size {
                Expr::IntLiteral(size) => {
                    if size as usize != items.len() {
                        self.diagnostics.push(LoweringDiagnostic {
                            kind: LoweringDiagnosticKind::ArraySizeMismatch {
                                found: items.len() as u32,
                                expected: size as u32,
                            },
                            range: array_expr.body(self.tree).unwrap().range(self.tree),
                        });
                    }
                    Some(size)
                }
                _ => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::TyParseError(TyParseError::ArraySizeNotConst),
                        range: array_expr.size(self.tree).unwrap().range(self.tree),
                    });
                    None
                }
            });

        Expr::Array {
            size,
            items,
            ty: self.twr_arena.alloc(ty),
        }
    }

    fn lower_block(&mut self, block: ast::Block) -> Expr {
        self.create_new_child_scope();

        let mut stmts = Vec::new();

        for stmt in block.stmts(self.tree) {
            let statement = self.lower_stmt(stmt);
            stmts.push(self.bodies.stmts.alloc(statement));
        }

        let tail_expr = block
            .tail_expr(self.tree)
            .map(|tail_expr| self.lower_expr(Some(tail_expr)));

        self.destroy_current_scope();

        Expr::Block { stmts, tail_expr }
    }

    fn lower_if(&mut self, if_expr: ast::IfExpr) -> Expr {
        let condition = self.lower_expr(if_expr.condition(self.tree));

        let body = self.lower_expr(if_expr.body(self.tree));

        let else_branch = if let Some(else_branch) = if_expr.else_branch(self.tree) {
            Some(self.lower_expr(else_branch.body(self.tree)))
        } else {
            None
        };

        Expr::If {
            condition,
            body,
            else_branch,
        }
    }

    fn lower_while(&mut self, while_expr: ast::WhileExpr) -> Expr {
        let condition = while_expr
            .condition(self.tree)
            .and_then(|condition| condition.value(self.tree))
            .map(|condition| self.lower_expr(Some(condition)));

        let body = self.lower_expr(while_expr.body(self.tree));

        Expr::While { condition, body }
    }

    fn lower_call(&mut self, call: ast::Call) -> Expr {
        let callee = self.lower_expr(call.callee(self.tree));

        let mut args = Vec::new();

        if let Some(arg_list) = call.arg_list(self.tree) {
            for arg in arg_list.args(self.tree) {
                let expr = self.lower_expr(arg.value(self.tree));
                args.push(expr);
            }
        }

        Expr::Call { callee, args }
    }

    fn lower_index_expr(&mut self, index_expr: ast::IndexExpr) -> Expr {
        let array = match index_expr.array(self.tree) {
            Some(array) => self.lower_expr(array.value(self.tree)),
            None => unreachable!(),
        };
        let index = match index_expr.index(self.tree) {
            Some(index) => self.lower_expr(index.value(self.tree)),
            None => unreachable!(),
        };

        Expr::Index { array, index }
    }

    fn lower_var_ref(&mut self, var_ref: ast::VarRef) -> Expr {
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

            let fqn = Fqn {
                module: Name(module_name),
                name: Name(var_name),
            };

            match self.world_index.get_definition(fqn) {
                Ok(def) => {
                    let path = PathWithRange::OtherModule {
                        fqn,
                        module_range: module_name_token.range(self.tree),
                        name_range: var_name_token.range(self.tree),
                    };

                    self.bodies.other_module_references.insert(fqn);

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Module(Name(module_name)));

                    match def {
                        Definition::Function(_) => {
                            self.bodies
                                .symbol_map
                                .insert(var_name_token, Symbol::Function(path.path()));
                        }
                        Definition::Global(_) => {
                            self.bodies
                                .symbol_map
                                .insert(var_name_token, Symbol::Global(path.path()));
                        }
                    }

                    self.bodies
                        .symbol_map
                        .insert(var_name_token, Symbol::Global(path.path()));

                    return Expr::Global(path);
                }
                Err(GetDefinitionError::UnknownModule) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::UndefinedModule { name: module_name },
                        range: module_name_token.range(self.tree),
                    });

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Unknown);
                    self.bodies
                        .symbol_map
                        .insert(var_name_token, Symbol::Unknown);

                    return Expr::Missing;
                }
                Err(GetDefinitionError::UnknownDefinition) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::UndefinedLocal { name: var_name },
                        range: var_name_token.range(self.tree),
                    });

                    self.bodies
                        .symbol_map
                        .insert(module_name_token, Symbol::Module(Name(module_name)));
                    self.bodies
                        .symbol_map
                        .insert(var_name_token, Symbol::Unknown);

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
        if self
            .world_index
            .get_definition(Fqn {
                module: self.module,
                name,
            })
            .is_ok()
        {
            let path = PathWithRange::ThisModule {
                name,
                range: ident.range(self.tree),
            };

            self.bodies
                .symbol_map
                .insert(ident, Symbol::Global(path.path()));

            return Expr::Global(path);
        }

        if let Some(ty) = TyWithRange::from_key(name.0, ident.range(self.tree)) {
            let ty = self.twr_arena.alloc(ty);

            self.bodies
                .symbol_map
                .insert(ident, Symbol::PrimitiveTy(ty));

            return Expr::PrimitiveTy { ty };
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::UndefinedLocal { name: name.0 },
            range: ident.range(self.tree),
        });

        self.bodies.symbol_map.insert(ident, Symbol::Unknown);

        Expr::Missing
    }

    fn lower_int_literal(&mut self, int_literal: ast::IntLiteral) -> Expr {
        let value = int_literal
            .value(self.tree)
            .and_then(|int| int.text(self.tree).parse().ok());

        if let Some(value) = value {
            return Expr::IntLiteral(value);
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::OutOfRangeIntLiteral,
            range: int_literal.range(self.tree),
        });

        Expr::Missing
    }

    fn lower_float_literal(&mut self, float_literal: ast::FloatLiteral) -> Expr {
        let value = float_literal
            .value(self.tree)
            .and_then(|int| int.text(self.tree).parse().ok());

        if let Some(value) = value {
            return Expr::FloatLiteral(value);
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::OutOfRangeFloatLiteral,
            range: float_literal.range(self.tree),
        });

        Expr::Missing
    }

    fn lower_bool_literal(&mut self, bool_literal: ast::BoolLiteral) -> Expr {
        let value = bool_literal
            .value(self.tree)
            .and_then(|b| b.text(self.tree).parse().ok());

        if let Some(value) = value {
            return Expr::BoolLiteral(value);
        }

        unreachable!()
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
                        '0' => text.push('\0'),
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

    fn insert_into_current_scope(&mut self, name: Key, value: Idx<LocalDef>) {
        let last_scope = self.scopes.last_mut().unwrap();
        last_scope.insert(name, value);
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

    pub fn global(&self, name: Name) -> Idx<Expr> {
        self.globals[&name]
    }

    pub fn range_for_expr(&self, expr: Idx<Expr>) -> TextRange {
        self.expr_ranges[expr]
    }

    pub fn other_module_references(&self) -> &FxHashSet<Fqn> {
        &self.other_module_references
    }

    // todo: use this in a LSP
    pub fn symbol(&self, ident: ast::Ident) -> Option<Symbol> {
        self.symbol_map.get(&ident).copied()
    }

    fn shrink_to_fit(&mut self) {
        let Self {
            local_defs,
            stmts,
            exprs,
            function_bodies,
            other_module_references,
            symbol_map,
            ..
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

impl std::ops::Index<Idx<Assign>> for Bodies {
    type Output = Assign;

    fn index(&self, id: Idx<Assign>) -> &Self::Output {
        &self.assigns[id]
    }
}

impl std::ops::Index<Idx<Lambda>> for Bodies {
    type Output = Lambda;

    fn index(&self, id: Idx<Lambda>) -> &Self::Output {
        &self.lambdas[id]
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
    pub fn debug(
        &self,
        module_name: &str,
        twr_arena: &Arena<TyWithRange>,
        interner: &Interner,
        show_expr_idx: bool,
    ) -> String {
        let mut s = String::new();

        let mut globals: Vec<_> = self.globals.iter().collect();
        globals.sort_unstable_by_key(|(name, _)| *name);

        for (name, expr_id) in globals {
            s.push_str(&format!(
                "\n{}.{} := ",
                module_name,
                interner.lookup(name.0)
            ));
            write_expr(
                *expr_id,
                show_expr_idx,
                self,
                &mut s,
                twr_arena,
                interner,
                0,
            );
            s.push(';');
        }

        let mut function_bodies: Vec<_> = self.function_bodies.iter().collect();
        function_bodies.sort_unstable_by_key(|(name, _)| *name);

        for (name, expr_id) in function_bodies {
            s.push_str(&format!(
                "\n{}.{} := () -> ",
                module_name,
                interner.lookup(name.0)
            ));
            write_expr(
                *expr_id,
                show_expr_idx,
                self,
                &mut s,
                twr_arena,
                interner,
                0,
            );
            s.push(';');
        }

        if !self.other_module_references.is_empty() {
            let mut other_module_references: Vec<_> = self.other_module_references.iter().collect();
            other_module_references.sort_by_key(|fqn| {
                format!(
                    "{}.{}",
                    interner.lookup(fqn.module.0),
                    interner.lookup(fqn.name.0),
                )
            });

            s.push_str(&format!(
                "\nReferences to other modules in {}:",
                module_name
            ));
            for fqn in &other_module_references {
                s.push_str(&format!(
                    "\n- {}.{}",
                    interner.lookup(fqn.module.0),
                    interner.lookup(fqn.name.0)
                ));
            }
        }

        return s.trim().to_string();

        fn write_expr(
            idx: Idx<Expr>,
            show_idx: bool,
            bodies: &Bodies,
            s: &mut String,
            twr_arena: &Arena<TyWithRange>,
            interner: &Interner,
            mut indentation: usize,
        ) {
            if show_idx {
                s.push_str("\x1B[90m(\x1B[0m")
            }

            match &bodies[idx] {
                Expr::Missing => s.push_str("<missing>"),

                Expr::IntLiteral(n) => s.push_str(&format!("{}", n)),

                Expr::FloatLiteral(n) => s.push_str(&format!("{}", n)),

                Expr::BoolLiteral(b) => s.push_str(&format!("{}", b)),

                Expr::StringLiteral(content) => s.push_str(&format!("{content:?}")),

                Expr::Array { size, items, ty } => {
                    s.push('[');
                    if let Some(size) = size {
                        s.push_str(&size.to_string());
                    }
                    s.push(']');
                    s.push_str(twr_arena[*ty].display(twr_arena, interner).as_str());

                    s.push('{');

                    for (idx, item) in items.iter().enumerate() {
                        s.push(' ');
                        write_expr(*item, show_idx, bodies, s, twr_arena, interner, indentation);
                        if idx != items.len() - 1 {
                            s.push(',');
                        }
                    }

                    s.push_str(" }");
                }

                Expr::Index { array, index } => {
                    write_expr(
                        *array,
                        show_idx,
                        bodies,
                        s,
                        twr_arena,
                        interner,
                        indentation,
                    );
                    s.push('[');
                    write_expr(
                        *index,
                        show_idx,
                        bodies,
                        s,
                        twr_arena,
                        interner,
                        indentation,
                    );
                    s.push(']');
                }

                Expr::Cast { expr, ty } => {
                    write_expr(*expr, show_idx, bodies, s, twr_arena, interner, indentation);

                    s.push_str(" as ");

                    s.push_str(twr_arena[*ty].display(twr_arena, interner).as_str());
                }

                Expr::Ref { mutable, expr } => {
                    s.push('^');

                    if *mutable {
                        s.push_str("mut ");
                    }

                    write_expr(*expr, show_idx, bodies, s, twr_arena, interner, indentation);
                }

                Expr::Deref { pointer } => {
                    write_expr(
                        *pointer,
                        show_idx,
                        bodies,
                        s,
                        twr_arena,
                        interner,
                        indentation,
                    );

                    s.push('^');
                }

                Expr::Binary { lhs, rhs, op } => {
                    write_expr(*lhs, show_idx, bodies, s, twr_arena, interner, indentation);

                    s.push(' ');

                    match op {
                        BinaryOp::Add => s.push('+'),
                        BinaryOp::Sub => s.push('-'),
                        BinaryOp::Mul => s.push('*'),
                        BinaryOp::Div => s.push('/'),
                        BinaryOp::Mod => s.push('%'),
                        BinaryOp::Lt => s.push('<'),
                        BinaryOp::Gt => s.push('>'),
                        BinaryOp::Le => s.push_str("<="),
                        BinaryOp::Ge => s.push_str(">="),
                        BinaryOp::Eq => s.push_str("=="),
                        BinaryOp::Ne => s.push_str("!="),
                        BinaryOp::And => s.push_str("&&"),
                        BinaryOp::Or => s.push_str("||"),
                    }

                    s.push(' ');

                    write_expr(*rhs, show_idx, bodies, s, twr_arena, interner, indentation);
                }

                Expr::Unary { expr, op } => {
                    match op {
                        UnaryOp::Pos => s.push('+'),
                        UnaryOp::Neg => s.push('-'),
                        UnaryOp::Not => s.push('!'),
                    }

                    write_expr(*expr, show_idx, bodies, s, twr_arena, interner, indentation);
                }

                Expr::Block {
                    stmts,
                    tail_expr: None,
                } if stmts.is_empty() => {
                    s.push_str("{}");
                }

                Expr::Block {
                    stmts,
                    tail_expr: Some(tail_expr),
                } if stmts.is_empty() => {
                    let mut inner = String::new();
                    write_expr(
                        *tail_expr,
                        show_idx,
                        bodies,
                        &mut inner,
                        twr_arena,
                        interner,
                        indentation + 4,
                    );

                    if inner.len() > 60 {
                        s.push_str("{\n");
                        s.push_str(&" ".repeat(indentation + 4));
                    } else {
                        s.push_str("{ ");
                    }

                    s.push_str(&inner);

                    if inner.len() > 60 {
                        s.push('\n');

                        s.push_str(&" ".repeat(indentation));

                        s.push('}');
                    } else {
                        s.push_str(" }");
                    }
                }

                Expr::Block { stmts, tail_expr } => {
                    indentation += 4;

                    s.push_str("{\n");

                    for stmt in stmts.clone() {
                        s.push_str(&" ".repeat(indentation));
                        write_stmt(stmt, show_idx, bodies, s, twr_arena, interner, indentation);
                        s.push('\n');
                    }

                    if let Some(tail_expr) = tail_expr {
                        s.push_str(&" ".repeat(indentation));
                        write_expr(
                            *tail_expr,
                            show_idx,
                            bodies,
                            s,
                            twr_arena,
                            interner,
                            indentation,
                        );
                        s.push('\n');
                    }

                    indentation -= 4;
                    s.push_str(&" ".repeat(indentation));

                    s.push('}');
                }

                Expr::If {
                    condition,
                    body,
                    else_branch,
                } => {
                    s.push_str("if ");
                    write_expr(
                        *condition,
                        show_idx,
                        bodies,
                        s,
                        twr_arena,
                        interner,
                        indentation,
                    );
                    s.push(' ');
                    write_expr(*body, show_idx, bodies, s, twr_arena, interner, indentation);
                    if let Some(else_branch) = else_branch {
                        s.push_str(" else ");
                        write_expr(
                            *else_branch,
                            show_idx,
                            bodies,
                            s,
                            twr_arena,
                            interner,
                            indentation,
                        );
                    }
                }

                Expr::While { condition, body } => {
                    if let Some(condition) = condition {
                        s.push_str("while ");
                        write_expr(
                            *condition,
                            show_idx,
                            bodies,
                            s,
                            twr_arena,
                            interner,
                            indentation,
                        );
                        s.push(' ');
                    } else {
                        s.push_str("loop ");
                    }
                    write_expr(*body, show_idx, bodies, s, twr_arena, interner, indentation);
                }

                Expr::Local(id) => s.push_str(&format!("l{}", id.into_raw())),

                Expr::Param { idx } => s.push_str(&format!("p{}", idx)),

                Expr::Call { callee, args } => {
                    write_expr(
                        *callee,
                        show_idx,
                        bodies,
                        s,
                        twr_arena,
                        interner,
                        indentation,
                    );

                    s.push('(');
                    for (idx, arg) in args.iter().enumerate() {
                        if idx != 0 {
                            s.push_str(", ");
                        }

                        write_expr(*arg, show_idx, bodies, s, twr_arena, interner, indentation);
                    }
                    s.push(')');
                }

                Expr::Global(path) => s.push_str(&path.path().display(interner)),

                Expr::Lambda(lambda) => {
                    let Lambda { function, body } = &bodies.lambdas[*lambda];

                    s.push('(');
                    for (idx, param) in function.params.iter().enumerate() {
                        if let Some(name) = param.name {
                            s.push_str(interner.lookup(name.0));
                            s.push_str(": ");
                        }

                        s.push_str(twr_arena[param.ty].display(twr_arena, interner).as_str());

                        if idx != function.params.len() - 1 {
                            s.push_str(", ");
                        }
                    }
                    s.push_str(") -> ");

                    s.push_str(
                        twr_arena[function.return_ty]
                            .display(twr_arena, interner)
                            .as_str(),
                    );

                    s.push(' ');

                    write_expr(*body, show_idx, bodies, s, twr_arena, interner, indentation);
                }

                Expr::PrimitiveTy { ty } => {
                    s.push_str(&twr_arena[*ty].display(twr_arena, interner))
                }
            }

            if show_idx {
                s.push_str("\x1B[90m #");
                s.push_str(&idx.into_raw().to_string());
                s.push_str(")\x1B[0m")
            }
        }

        fn write_stmt(
            expr: Idx<Stmt>,
            show_idx: bool,
            bodies: &Bodies,
            s: &mut String,
            ty_arena: &Arena<TyWithRange>,
            interner: &Interner,
            indentation: usize,
        ) {
            match &bodies[expr] {
                Stmt::Expr(expr_id) => {
                    write_expr(
                        *expr_id,
                        show_idx,
                        bodies,
                        s,
                        ty_arena,
                        interner,
                        indentation,
                    );
                    s.push(';');
                }
                Stmt::LocalDef(local_def_id) => {
                    s.push_str(&format!("l{} := ", local_def_id.into_raw()));
                    write_expr(
                        bodies[*local_def_id].value,
                        show_idx,
                        bodies,
                        s,
                        ty_arena,
                        interner,
                        indentation,
                    );
                    s.push(';');
                }
                Stmt::Assign(local_set_id) => {
                    write_expr(
                        bodies[*local_set_id].source,
                        show_idx,
                        bodies,
                        s,
                        ty_arena,
                        interner,
                        indentation,
                    );
                    s.push_str(" = ");
                    write_expr(
                        bodies[*local_set_id].value,
                        show_idx,
                        bodies,
                        s,
                        ty_arena,
                        interner,
                        indentation,
                    );
                    s.push(';');
                }
            }
        }
    }
}

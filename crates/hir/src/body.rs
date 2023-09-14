use std::{env, mem, vec};

use ast::{AstNode, AstToken};
use interner::{Interner, Key};
use la_arena::{Arena, ArenaMap, Idx};
use path_clean::PathClean;
use rustc_hash::{FxHashMap, FxHashSet};
use syntax::SyntaxTree;
use text_size::TextRange;

use crate::{
    nameres::Path, FileName, Fqn, Function, Index, Name, NameWithRange, Param, TyParseError,
    TyWithRange, UIDGenerator,
};

#[derive(Clone, Debug)]
pub struct Bodies {
    local_defs: Arena<LocalDef>,
    assigns: Arena<Assign>,
    stmts: Arena<Stmt>,
    exprs: Arena<Expr>,
    expr_ranges: ArenaMap<Idx<Expr>, TextRange>,
    function_bodies: FxHashMap<Name, Idx<Expr>>,
    globals: FxHashMap<Name, Idx<Expr>>,
    lambdas: Arena<Lambda>,
    comptimes: Arena<Comptime>,
    imports: FxHashSet<FileName>,
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
        ty: Idx<Expr>,
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
        ty: Idx<Expr>,
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
    SelfGlobal(NameWithRange),
    Param {
        idx: u32,
        range: TextRange,
    },
    Path {
        previous: Idx<Expr>,
        field: NameWithRange,
    },
    Call {
        callee: Idx<Expr>,
        args: Vec<Idx<Expr>>,
    },
    Lambda(Idx<Lambda>),
    Comptime(Idx<Comptime>),
    /// either a primitive type (such as `i32`, `bool`, etc.), or an array type,
    /// or a pointer to a primitive type, or a distinct type
    PrimitiveTy {
        ty: Idx<TyWithRange>,
    },
    StructLiteral {
        ty: Idx<Expr>,
        fields: Vec<(Option<NameWithRange>, Idx<Expr>)>,
    },
    Import(FileName),
}

#[derive(Debug, Clone)]
pub struct Lambda {
    pub function: Function,
    pub body: Idx<Expr>,
}

#[derive(Debug, Clone, Copy)]
pub struct Comptime {
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

#[derive(Clone, Debug)]
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

#[derive(Debug, Clone, Copy, PartialEq)]
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
    UndefinedRef { name: Key },
    NonGlobalExtern,
    ArraySizeMismatch { found: u32, expected: u32 },
    InvalidEscape,
    ImportMustEndInDotCapy,
    ImportDoesNotExist { file: String },
    TyParseError(TyParseError),
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

#[allow(clippy::too_many_arguments)]
pub fn lower(
    root: ast::Root,
    tree: &SyntaxTree,
    file_name: &std::path::Path,
    index: &Index,
    uid_gen: &mut UIDGenerator,
    twr_arena: &mut Arena<TyWithRange>,
    interner: &mut Interner,
    fake_file_system: bool,
) -> (Bodies, Vec<LoweringDiagnostic>) {
    let mut ctx = Ctx::new(
        file_name,
        index,
        uid_gen,
        twr_arena,
        interner,
        tree,
        fake_file_system,
    );

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
    file_name: &'a std::path::Path,
    index: &'a Index,
    uid_gen: &'a mut UIDGenerator,
    twr_arena: &'a mut Arena<TyWithRange>,
    interner: &'a mut Interner,
    tree: &'a SyntaxTree,
    diagnostics: Vec<LoweringDiagnostic>,
    scopes: Vec<FxHashMap<Key, Idx<LocalDef>>>,
    params: FxHashMap<Key, (u32, ast::Param)>,
    fake_file_system: bool, // used for importing files in tests
}

impl<'a> Ctx<'a> {
    fn new(
        file_name: &'a std::path::Path,
        index: &'a Index,
        uid_gen: &'a mut UIDGenerator,
        twr_arena: &'a mut Arena<TyWithRange>,
        interner: &'a mut Interner,
        tree: &'a SyntaxTree,
        fake_file_system: bool,
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
                comptimes: Arena::new(),
                imports: FxHashSet::default(),
            },
            file_name,
            index,
            uid_gen,
            twr_arena,
            interner,
            tree,
            diagnostics: Vec::new(),
            scopes: vec![FxHashMap::default()],
            params: FxHashMap::default(),
            fake_file_system,
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
        if lambda.body(self.tree).is_none() && lambda.r#extern(self.tree).is_none() {
            match TyWithRange::parse(
                Some(ast::Expr::Lambda(lambda)),
                self.uid_gen,
                self.twr_arena,
                self.interner,
                self.tree,
                false,
            ) {
                Ok(ty) => {
                    return Expr::PrimitiveTy {
                        ty: self.twr_arena.alloc(ty),
                    }
                }
                Err((why, range)) => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::TyParseError(why),
                        range,
                    });

                    return Expr::Missing;
                }
            }
        }

        let old_params = mem::take(&mut self.params);
        let old_scopes = mem::take(&mut self.scopes);

        let mut params = Vec::new();
        let mut param_type_ranges = Vec::new();

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
        self.scopes = old_scopes;

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
                is_extern: lambda.r#extern(self.tree).is_some(), // this doesn't matter since lambdas can't be extern
            },
            body,
        }))
    }

    fn lower_comptime(&mut self, comptime_expr: ast::ComptimeExpr) -> Expr {
        let old_params = mem::take(&mut self.params);
        let old_scopes = mem::take(&mut self.scopes);

        let body = self.lower_expr(comptime_expr.body(self.tree));

        self.params = old_params;
        self.scopes = old_scopes;

        Expr::Comptime(self.bodies.comptimes.alloc(Comptime { body }))
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
            ast::Expr::Path(path) => self.lower_path(path),
            ast::Expr::IntLiteral(int_literal) => self.lower_int_literal(int_literal),
            ast::Expr::FloatLiteral(float_literal) => self.lower_float_literal(float_literal),
            ast::Expr::BoolLiteral(bool_literal) => self.lower_bool_literal(bool_literal),
            ast::Expr::StringLiteral(string_literal) => self.lower_string_literal(string_literal),
            ast::Expr::Distinct(distinct) => self.lower_distinct(distinct),
            ast::Expr::Lambda(lambda) => self.lower_lambda(lambda),
            ast::Expr::StructDecl(struct_decl) => self.lower_struct_declaration(struct_decl),
            ast::Expr::StructLiteral(struct_lit) => self.lower_struct_literal(struct_lit),
            ast::Expr::Import(import_expr) => self.lower_import(import_expr),
            ast::Expr::Comptime(comptime_expr) => self.lower_comptime(comptime_expr),
        }
    }

    fn lower_cast_expr(&mut self, cast_expr: ast::CastExpr) -> Expr {
        let expr = self.lower_expr(cast_expr.expr(self.tree));
        let ty = self.lower_expr(cast_expr.ty(self.tree).and_then(|ty| ty.expr(self.tree)));

        Expr::Cast { expr, ty }
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

    fn lower_struct_declaration(&mut self, struct_decl: ast::StructDeclaration) -> Expr {
        let ty = match TyWithRange::parse(
            Some(ast::Expr::StructDecl(struct_decl)),
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

    fn lower_struct_literal(&mut self, struct_lit: ast::StructLiteral) -> Expr {
        let ty = self.lower_expr(struct_lit.ty(self.tree).and_then(|ty| ty.expr(self.tree)));

        let mut fields = Vec::new();

        for field in struct_lit.fields(self.tree) {
            let name = field.name(self.tree).map(|ident| NameWithRange {
                name: Name(self.interner.intern(ident.text(self.tree))),
                range: ident.range(self.tree),
            });

            let value = self.lower_expr(field.value(self.tree));

            fields.push((name, value));
        }

        Expr::StructLiteral { ty, fields }
    }

    fn lower_import(&mut self, import: ast::ImportExpr) -> Expr {
        let file_name = match import.file(self.tree) {
            Some(file_name) => file_name,
            None => return Expr::Missing,
        };
        let old_diags_len = self.diagnostics.len();
        let file = match self.lower_string_literal(file_name) {
            Expr::StringLiteral(text) => text.replace(['/', '\\'], std::path::MAIN_SEPARATOR_STR),
            _ => unreachable!(),
        };
        if self.diagnostics.len() != old_diags_len {
            return Expr::Missing;
        }
        if !file.ends_with(".capy") {
            self.diagnostics.push(LoweringDiagnostic {
                kind: LoweringDiagnosticKind::ImportMustEndInDotCapy,
                range: file_name.range(self.tree),
            });
            return Expr::Missing;
        }

        let file = if !self.fake_file_system {
            let file = std::path::Path::new(&file);

            let file = env::current_dir()
                .unwrap()
                .join(self.file_name)
                .join("..")
                .join(file)
                .clean();

            if !file.exists() || !file.is_file() {
                self.diagnostics.push(LoweringDiagnostic {
                    kind: LoweringDiagnosticKind::ImportDoesNotExist {
                        file: file.to_string_lossy().to_string(),
                    },
                    range: file_name.range(self.tree),
                });
                return Expr::Missing;
            }

            file
        } else {
            file.into()
        };

        let file_name = FileName(self.interner.intern(&file.to_string_lossy()));

        // println!(
        //     r#"{:?} = "{}""#,
        //     file_name,
        //     self.interner.lookup(file_name.0)
        // );

        self.bodies.imports.insert(file_name);
        Expr::Import(file_name)
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
        let ty = self.lower_expr(array_expr.ty(self.tree).and_then(|ty| ty.expr(self.tree)));

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

        let size = array_expr
            .size(self.tree)
            .and_then(|size| size.size(self.tree))
            .and_then(|size| match size {
                ast::Expr::IntLiteral(_) => Some(self.lower_expr_raw(size)),
                other => {
                    self.diagnostics.push(LoweringDiagnostic {
                        kind: LoweringDiagnosticKind::TyParseError(TyParseError::ArraySizeNotConst),
                        range: other.range(self.tree),
                    });
                    None
                }
            })
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
                _ => unreachable!(), // this was already filtered out
            });

        Expr::Array { size, items, ty }
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

    fn lower_path(&mut self, path: ast::Path) -> Expr {
        let field = match path.field_name(self.tree) {
            Some(field) => field,
            None => return Expr::Missing,
        };
        let field_name = self.interner.intern(field.text(self.tree));

        let previous = path.previous_part(self.tree);

        Expr::Path {
            previous: self.lower_expr(previous),
            field: NameWithRange {
                name: Name(field_name),
                range: field.range(self.tree),
            },
        }
    }

    fn lower_var_ref(&mut self, var_ref: ast::VarRef) -> Expr {
        let ident = match var_ref.name(self.tree) {
            Some(ident) => ident,
            None => return Expr::Missing,
        };
        let ident_name = self.interner.intern(ident.text(self.tree));

        // only have one ident as path
        if let Some(def) = self.look_up_in_current_scope(ident_name) {
            return Expr::Local(def);
        }

        if let Some((idx, ast)) = self.look_up_param(ident_name) {
            return Expr::Param {
                idx,
                range: ast.range(self.tree),
            };
        }

        let name = Name(ident_name);
        if self.index.get_definition(name).is_some() {
            return Expr::SelfGlobal(NameWithRange {
                name,
                range: ident.range(self.tree),
            });
        }

        if let Some(ty) = TyWithRange::from_key(name.0, ident.range(self.tree)) {
            let ty = self.twr_arena.alloc(ty);

            return Expr::PrimitiveTy { ty };
        }

        self.diagnostics.push(LoweringDiagnostic {
            kind: LoweringDiagnosticKind::UndefinedRef { name: name.0 },
            range: ident.range(self.tree),
        });

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
            .and_then(|int| int.text(self.tree).parse().ok())
            .unwrap();

        Expr::FloatLiteral(value)
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
                        '0' => text.push('\0'),   // null
                        'a' => text.push('\x07'), // bell (BEL)
                        'b' => text.push('\x08'), // backspace
                        'n' => text.push('\n'),   // line feed (new line)
                        'f' => text.push('\x0C'), // form feed (new page)
                        'r' => text.push('\r'),   // carraige return
                        't' => text.push('\t'),   // horizontal tab
                        'v' => text.push('\x0B'), // vertical tab
                        'e' => text.push('\x1B'), // escape
                        '"' => text.push('"'),
                        '\\' => text.push('\\'),
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

    pub fn get_range_for_expr(&self, expr: Idx<Expr>) -> Option<TextRange> {
        self.expr_ranges.get(expr).copied()
    }

    pub fn comptimes(&self) -> impl Iterator<Item = Idx<Comptime>> + '_ {
        self.comptimes.iter().map(|(idx, _)| idx)
    }

    pub fn imports(&self) -> &FxHashSet<FileName> {
        &self.imports
    }

    fn shrink_to_fit(&mut self) {
        let Self {
            local_defs,
            stmts,
            exprs,
            function_bodies,
            assigns,
            expr_ranges: _,
            globals,
            lambdas,
            comptimes,
            imports,
        } = self;

        local_defs.shrink_to_fit();
        stmts.shrink_to_fit();
        exprs.shrink_to_fit();
        function_bodies.shrink_to_fit();
        assigns.shrink_to_fit();
        globals.shrink_to_fit();
        lambdas.shrink_to_fit();
        comptimes.shrink_to_fit();
        imports.shrink_to_fit();
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

impl std::ops::Index<Idx<Comptime>> for Bodies {
    type Output = Comptime;

    fn index(&self, id: Idx<Comptime>) -> &Self::Output {
        &self.comptimes[id]
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
        module: FileName,
        twr_arena: &Arena<TyWithRange>,
        project_root: &std::path::Path,
        interner: &Interner,
        show_expr_idx: bool,
    ) -> String {
        let mut s = String::new();

        let mut globals: Vec<_> = self.globals.iter().collect();
        globals.sort_unstable_by_key(|(name, _)| *name);

        for (name, expr_id) in globals {
            s.push_str(&format!(
                "{} := ",
                Fqn {
                    module,
                    name: *name,
                }
                .to_string(project_root, interner)
            ));
            write_expr(
                &mut s,
                *expr_id,
                show_expr_idx,
                self,
                twr_arena,
                project_root,
                interner,
                0,
            );
            s.push_str(";\n");
        }

        let mut function_bodies: Vec<_> = self.function_bodies.iter().collect();
        function_bodies.sort_unstable_by_key(|(name, _)| *name);

        for (name, expr_id) in function_bodies {
            s.push_str(&format!(
                "{} := () -> ",
                Fqn {
                    module,
                    name: *name,
                }
                .to_string(project_root, interner)
            ));
            write_expr(
                &mut s,
                *expr_id,
                show_expr_idx,
                self,
                twr_arena,
                project_root,
                interner,
                0,
            );
            s.push_str(";\n");
        }

        return s;

        #[allow(clippy::too_many_arguments)]
        fn write_expr(
            s: &mut String,
            idx: Idx<Expr>,
            show_idx: bool,
            bodies: &Bodies,
            twr_arena: &Arena<TyWithRange>,
            project_root: &std::path::Path,
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
                    write_expr(
                        s,
                        *ty,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

                    s.push('{');

                    for (idx, item) in items.iter().enumerate() {
                        s.push(' ');
                        write_expr(
                            s,
                            *item,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
                            interner,
                            indentation,
                        );
                        if idx != items.len() - 1 {
                            s.push(',');
                        }
                    }

                    s.push_str(" }");
                }

                Expr::Index { array, index } => {
                    write_expr(
                        s,
                        *array,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push('[');
                    write_expr(
                        s,
                        *index,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push(']');
                }

                Expr::Cast { expr, ty } => {
                    write_expr(
                        s,
                        *expr,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

                    s.push_str(" as ");

                    write_expr(
                        s,
                        *ty,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                }

                Expr::Ref { mutable, expr } => {
                    s.push('^');

                    if *mutable {
                        s.push_str("mut ");
                    }

                    write_expr(
                        s,
                        *expr,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                }

                Expr::Deref { pointer } => {
                    write_expr(
                        s,
                        *pointer,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

                    s.push('^');
                }

                Expr::Binary { lhs, rhs, op } => {
                    write_expr(
                        s,
                        *lhs,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

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

                    write_expr(
                        s,
                        *rhs,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                }

                Expr::Unary { expr, op } => {
                    match op {
                        UnaryOp::Pos => s.push('+'),
                        UnaryOp::Neg => s.push('-'),
                        UnaryOp::Not => s.push('!'),
                    }

                    write_expr(
                        s,
                        *expr,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
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
                        &mut inner,
                        *tail_expr,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
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
                        write_stmt(
                            s,
                            stmt,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
                            interner,
                            indentation,
                        );
                        s.push('\n');
                    }

                    if let Some(tail_expr) = tail_expr {
                        s.push_str(&" ".repeat(indentation));
                        write_expr(
                            s,
                            *tail_expr,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
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
                        s,
                        *condition,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push(' ');
                    write_expr(
                        s,
                        *body,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    if let Some(else_branch) = else_branch {
                        s.push_str(" else ");
                        write_expr(
                            s,
                            *else_branch,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
                            interner,
                            indentation,
                        );
                    }
                }

                Expr::While { condition, body } => {
                    if let Some(condition) = condition {
                        s.push_str("while ");
                        write_expr(
                            s,
                            *condition,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
                            interner,
                            indentation,
                        );
                        s.push(' ');
                    } else {
                        s.push_str("loop ");
                    }
                    write_expr(
                        s,
                        *body,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                }

                Expr::Local(id) => s.push_str(&format!("l{}", id.into_raw())),

                Expr::Param { idx, .. } => s.push_str(&format!("p{}", idx)),

                Expr::Call { callee, args } => {
                    write_expr(
                        s,
                        *callee,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

                    s.push('(');
                    for (idx, arg) in args.iter().enumerate() {
                        if idx != 0 {
                            s.push_str(", ");
                        }

                        write_expr(
                            s,
                            *arg,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
                            interner,
                            indentation,
                        );
                    }
                    s.push(')');
                }

                Expr::SelfGlobal(name) => s.push_str(interner.lookup(name.name.0)),

                Expr::Path {
                    previous, field, ..
                } => {
                    write_expr(
                        s,
                        *previous,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

                    s.push('.');

                    s.push_str(interner.lookup(field.name.0));
                }

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

                    write_expr(
                        s,
                        *body,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                }

                Expr::Comptime(comptime) => {
                    let Comptime { body } = bodies.comptimes[*comptime];

                    s.push_str("comptime ");

                    write_expr(
                        s,
                        body,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                }

                Expr::StructLiteral { ty, fields } => {
                    write_expr(
                        s,
                        *ty,
                        show_idx,
                        bodies,
                        twr_arena,
                        project_root,
                        interner,
                        indentation,
                    );

                    s.push_str(" {");

                    for (idx, (name, value)) in fields.iter().enumerate() {
                        if let Some(name) = name {
                            s.push_str(interner.lookup(name.name.0));
                            s.push_str(": ");
                        }

                        write_expr(
                            s,
                            *value,
                            show_idx,
                            bodies,
                            twr_arena,
                            project_root,
                            interner,
                            indentation,
                        );

                        if idx != fields.len() - 1 {
                            s.push_str(", ");
                        }
                    }

                    s.push('}');
                }

                Expr::PrimitiveTy { ty } => {
                    s.push_str(&twr_arena[*ty].display(twr_arena, interner))
                }

                Expr::Import(file_name) => {
                    s.push_str(&format!(r#"import "{}""#, interner.lookup(file_name.0)))
                }
            }

            if show_idx {
                s.push_str("\x1B[90m #");
                s.push_str(&idx.into_raw().to_string());
                s.push_str(")\x1B[0m")
            }
        }

        #[allow(clippy::too_many_arguments)]
        fn write_stmt(
            s: &mut String,
            expr: Idx<Stmt>,
            show_idx: bool,
            bodies: &Bodies,
            ty_arena: &Arena<TyWithRange>,
            project_root: &std::path::Path,
            interner: &Interner,
            indentation: usize,
        ) {
            match &bodies[expr] {
                Stmt::Expr(expr_id) => {
                    write_expr(
                        s,
                        *expr_id,
                        show_idx,
                        bodies,
                        ty_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push(';');
                }
                Stmt::LocalDef(local_def_id) => {
                    s.push_str(&format!("l{} := ", local_def_id.into_raw()));
                    write_expr(
                        s,
                        bodies[*local_def_id].value,
                        show_idx,
                        bodies,
                        ty_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push(';');
                }
                Stmt::Assign(local_set_id) => {
                    write_expr(
                        s,
                        bodies[*local_set_id].source,
                        show_idx,
                        bodies,
                        ty_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push_str(" = ");
                    write_expr(
                        s,
                        bodies[*local_set_id].value,
                        show_idx,
                        bodies,
                        ty_arena,
                        project_root,
                        interner,
                        indentation,
                    );
                    s.push(';');
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};

    fn check<const N: usize>(
        input: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(
            &mut Interner,
        ) -> [(LoweringDiagnosticKind, std::ops::Range<u32>); N],
    ) {
        let mut interner = Interner::default();
        let mut uid_gen = UIDGenerator::default();
        let mut twr_arena = Arena::default();

        let tokens = lexer::lex(input);
        let tree = parser::parse_source_file(&tokens, input).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = crate::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

        let (bodies, actual_diagnostics) = lower(
            root,
            &tree,
            std::path::Path::new("main.capy"),
            &index,
            &mut uid_gen,
            &mut twr_arena,
            &mut interner,
            true,
        );

        expect.assert_eq(&bodies.debug(
            FileName(interner.intern("main.capy")),
            &twr_arena,
            std::path::Path::new(""),
            &interner,
            false,
        ));

        let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
            .into_iter()
            .map(|(kind, range)| LoweringDiagnostic {
                kind,
                range: TextRange::new(range.start.into(), range.end.into()),
            })
            .collect();

        assert_eq!(expected_diagnostics, actual_diagnostics);
    }

    #[test]
    fn empty() {
        check("", expect![""], |_| [])
    }

    #[test]
    fn function() {
        check(
            r#"
                foo :: () {
                    
                }
            "#,
            expect![[r#"
                main::foo := () -> {};
            "#]],
            |_| [],
        )
    }

    #[test]
    fn binary() {
        check(
            r#"
                foo :: () {
                    1 + 1;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    1 + 1;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn global() {
        check(
            r#"
                foo :: 5;

                bar :: () {
                    foo;
                }
            "#,
            expect![[r#"
                main::foo := 5;
                main::bar := () -> {
                    foo;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn local_var() {
        check(
            r#"
                foo :: () {
                    x := 5;

                    x;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := 5;
                    l0;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn param() {
        check(
            r#"
                foo :: (x: i32) {
                    x;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    p0;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn import() {
        check(
            r#"
                other_file :: import "other_file.capy";

                foo :: () {
                    other_file.global;
                }
            "#,
            expect![[r#"
                main::other_file := import "other_file.capy";
                main::foo := () -> {
                    other_file.global;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn import_non_dot_capy() {
        check(
            r#"
                foo :: () {
                    other_file :: import "other_file.cap";

                    other_file.global;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := <missing>;
                    l0.global;
                };
            "#]],
            |_| [(LoweringDiagnosticKind::ImportMustEndInDotCapy, 70..86)],
        )
    }

    #[test]
    fn int_literal() {
        check(
            r#"
                foo :: () {
                    num := 18446744073709551615;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := 18446744073709551615;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn out_of_range_int_literal() {
        check(
            r#"
                foo :: () {
                    num := 18446744073709551616;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := <missing>;
                };
            "#]],
            |_| [(LoweringDiagnosticKind::OutOfRangeIntLiteral, 56..76)],
        )
    }

    #[test]
    fn float_literal() {
        check(
            r#"
                foo :: () {
                    num := .123;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := 0.123;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn string_literal() {
        check(
            r#"
                foo :: () {
                    crab := "🦀";
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := "🦀";
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn string_literal_with_escapes() {
        check(
            r#"
                foo :: () {
                    crab := "\0\a\b\n\f\r\t\v\e\"\\";
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := "\0\u{7}\u{8}\n\u{c}\r\t\u{b}\u{1b}\"\\";
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn string_literal_with_invalid_escapes() {
        check(
            r#"
                foo :: () {
                    crab := "a\jb\🦀c";
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := "abc";
                };
            "#]],
            |_| {
                [
                    (LoweringDiagnosticKind::InvalidEscape, 59..61),
                    (LoweringDiagnosticKind::InvalidEscape, 62..67),
                ]
            },
        )
    }

    #[test]
    fn nested_binary_expr() {
        check(
            r#"
                foo :: () -> i32 {
                    1 + 2 * 3 - 4 / 5
                }
            "#,
            expect![[r#"
                main::foo := () -> { 1 + 2 * 3 - 4 / 5 };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn multiple_local_defs() {
        check(
            r#"
                foo :: () {
                    a := 1;
                    b := 2;
                    c := 3;
                    d := 4;
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := 1;
                    l1 := 2;
                    l2 := 3;
                    l3 := 4;
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn multiple_functions() {
        check(
            r#"
                foo :: () {}
                bar :: () {}
                baz :: () {}
                qux :: () {}
            "#,
            expect![[r#"
                main::foo := () -> {};
                main::bar := () -> {};
                main::baz := () -> {};
                main::qux := () -> {};
            "#]],
            |_| [],
        )
    }

    #[test]
    fn call_other_function() {
        check(
            r#"
                foo :: () {
                    bar()
                }

                bar :: () {
                    foo()
                }
            "#,
            expect![[r#"
                main::foo := () -> { bar() };
                main::bar := () -> { foo() };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn call_non_existent_function() {
        check(
            r#"
                foo :: () {
                    bar()
                }
            "#,
            expect![[r#"
                main::foo := () -> { <missing>() };
            "#]],
            |i| {
                [(
                    LoweringDiagnosticKind::UndefinedRef {
                        name: i.intern("bar"),
                    },
                    49..52,
                )]
            },
        )
    }

    #[test]
    fn recursion() {
        check(
            r#"
                foo :: () {
                    foo();
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    foo();
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn lambda() {
        check(
            r#"
                foo :: () {
                    bar := () {};
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := () -> void {};
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn lambda_dont_capture_scope() {
        check(
            r#"
                foo :: (x: i32) {
                    y := 5;

                    bar := () -> i32 {
                        x + y
                    };
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    l0 := 5;
                    l1 := () -> i32 { <missing> + <missing> };
                };
            "#]],
            |i| {
                [
                    (
                        LoweringDiagnosticKind::UndefinedRef {
                            name: i.intern("x"),
                        },
                        127..128,
                    ),
                    (
                        LoweringDiagnosticKind::UndefinedRef {
                            name: i.intern("y"),
                        },
                        131..132,
                    ),
                ]
            },
        )
    }

    #[test]
    fn call_lambda() {
        check(
            r#"
                foo :: () -> i32 {
                    {
                        (x: i32, y: i32) -> i32 {
                            x + y
                        }
                    } (1, 2)
                }
            "#,
            expect![[r#"
                main::foo := () -> { { (x: i32, y: i32) -> i32 { p0 + p1 } }(1, 2) };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn scoped_local() {
        check(
            r#"
                foo :: () -> i32 {
                    {
                        a := 5;
                    }

                    a
                }
            "#,
            expect![[r#"
                main::foo := () -> {
                    {
                        l0 := 5;
                    };
                    <missing>
                };
            "#]],
            |i| {
                [(
                    LoweringDiagnosticKind::UndefinedRef {
                        name: i.intern("a"),
                    },
                    133..134,
                )]
            },
        )
    }

    #[test]
    fn locals_take_precedence_over_functions() {
        check(
            r#"
                bar :: () -> i32 { 0 };

                foo :: () -> i32 {
                    bar := 25;

                    bar
                }
            "#,
            expect![[r#"
                main::bar := () -> { 0 };
                main::foo := () -> {
                    l0 := 25;
                    l0
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn locals_take_precedence_over_params() {
        check(
            r#"
                main :: () -> i32 {
                    foo := {
                        bar := {
                            baz := 9;
                            baz * 10
                        };
                        bar - 1
                    };
                    foo + 3
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l2 := {
                        l1 := {
                            l0 := 9;
                            l0 * 10
                        };
                        l1 - 1
                    };
                    l2 + 3
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn extern_lambda() {
        check(
            r#"
                main :: () -> i32 {
                    puts := (s: string) extern;
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := (s: string) -> void <missing>;
                };
            "#]],
            |_| [(LoweringDiagnosticKind::NonGlobalExtern, 77..83)],
        )
    }

    #[test]
    fn array_with_inferred_size() {
        check(
            r#"
                main :: () -> i32 {
                    my_array := [] i32 { 4, 8, 15, 16, 23, 42 };
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := []i32{ 4, 8, 15, 16, 23, 42 };
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn array_with_specific_size() {
        check(
            r#"
                main :: () -> i32 {
                    my_array := [6] i32 { 4, 8, 15, 16, 23, 42 };
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := [6]i32{ 4, 8, 15, 16, 23, 42 };
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn array_with_incorrect_size() {
        check(
            r#"
                main :: () -> i32 {
                    my_array := [3] i32 { 4, 8, 15, 16, 23, 42 };
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := [3]i32{ 4, 8, 15, 16, 23, 42 };
                };
            "#]],
            |_| {
                [(
                    LoweringDiagnosticKind::ArraySizeMismatch {
                        found: 6,
                        expected: 3,
                    },
                    77..101,
                )]
            },
        )
    }

    #[test]
    fn array_with_non_const_size() {
        check(
            r#"
                main :: () -> i32 {
                    size := 6;

                    my_array := [size] i32 { 4, 8, 15, 16, 23, 42 };
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := 6;
                    l1 := []i32{ 4, 8, 15, 16, 23, 42 };
                };
            "#]],
            |_| {
                [(
                    LoweringDiagnosticKind::TyParseError(TyParseError::ArraySizeNotConst),
                    102..106,
                )]
            },
        )
    }

    #[test]
    fn comptime() {
        check(
            r#"
                main :: () -> i32 {
                    num :: comptime {
                        1 + 1
                    };
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := comptime { 1 + 1 };
                };
            "#]],
            |_| [],
        )
    }

    #[test]
    fn comptime_dont_capture_scope() {
        check(
            r#"
                main :: (x: i32) -> i32 {
                    y := 5;

                    num :: comptime {
                        x + y
                    };
                }
            "#,
            expect![[r#"
                main::main := () -> {
                    l0 := 5;
                    l1 := comptime { <missing> + <missing> };
                };
            "#]],
            |i| {
                [
                    (
                        LoweringDiagnosticKind::UndefinedRef {
                            name: i.intern("x"),
                        },
                        134..135,
                    ),
                    (
                        LoweringDiagnosticKind::UndefinedRef {
                            name: i.intern("y"),
                        },
                        138..139,
                    ),
                ]
            },
        )
    }

    #[test]
    fn comptime_globals() {
        check(
            r#"
                foo :: 5;

                main :: () -> i32 {
                    num :: comptime {
                        foo * 2
                    };
                }
            "#,
            expect![[r#"
                main::foo := 5;
                main::main := () -> {
                    l0 := comptime { foo * 2 };
                };
            "#]],
            |_| [],
        )
    }
}

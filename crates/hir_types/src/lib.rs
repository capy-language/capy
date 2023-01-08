
use interner::{Key, Interner};
use la_arena::{ArenaMap, Idx};
use rustc_hash::FxHashMap;
use text_size::TextRange;

#[derive(Clone)]
pub struct InferenceResult {
    signatures: FxHashMap<hir::Name, Signature>,
    expr_types: ArenaMap<Idx<hir::Expr>, ResolvedType>,
    local_types: ArenaMap<Idx<hir::LocalDef>, ResolvedType>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ResolvedType {
    Unknown,
    S32,
    String,
    Named(hir::Fqn),
    Void,
}

impl std::ops::Index<Idx<hir::Expr>> for InferenceResult {
    type Output = ResolvedType;

    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        &self.expr_types[expr]
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for InferenceResult {
    type Output = ResolvedType;

    fn index(&self, local_def: Idx<hir::LocalDef>) -> &Self::Output {
        &self.local_types[local_def]
    }
}

#[derive(Clone)]
struct Signature {
    return_type: ResolvedType,
    param_types: Vec<ResolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDiagnostic {
    pub kind: TypeDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDiagnosticKind {
    Mismatch { expected: ResolvedType, found: ResolvedType },
    Undefined { name: Key },
}

pub fn infer_all(
    bodies: &hir::Bodies,
    index: &hir::Index,
    world_index: &hir::WorldIndex,
) -> (InferenceResult, Vec<TypeDiagnostic>) {
    let mut expr_types = ArenaMap::default();
    let mut local_types = ArenaMap::default();
    let mut diagnostics = Vec::new();
    let mut signatures = FxHashMap::default();

    for (name, function) in index.functions() {
        let signature = get_signature(
            function,
            hir::Path::ThisModule(name),
            index,
            world_index,
            &mut diagnostics,
        );

        FunctionInferenceCtx {
            expr_types: &mut expr_types,
            local_types: &mut local_types,
            param_types: &signature.param_types,
            bodies,
            index,
            world_index,
            diagnostics: &mut diagnostics,
        }
        .finish(name, &signature);

        signatures.insert(name, signature);
    }

    let mut result = InferenceResult { signatures, expr_types, local_types };
    result.shrink_to_fit();

    (result, diagnostics)
}

pub fn infer(
    function_name: hir::Name,
    bodies: &hir::Bodies,
    index: &hir::Index,
    world_index: &hir::WorldIndex,
) -> (InferenceResult, Vec<TypeDiagnostic>) {
    let function = match index.get_definition(function_name) {
        Some(hir::Definition::Function(f)) => f,
        Some(_) | None => panic!("passed non-function name"),
    };

    let mut expr_types = ArenaMap::default();
    let mut local_types = ArenaMap::default();
    let mut diagnostics = Vec::new();

    let signature = get_signature(
        function,
        hir::Path::ThisModule(function_name),
        index,
        world_index,
        &mut diagnostics,
    );

    FunctionInferenceCtx {
        expr_types: &mut expr_types,
        local_types: &mut local_types,
        param_types: &signature.param_types,
        bodies,
        index,
        world_index,
        diagnostics: &mut diagnostics,
    }
    .finish(function_name, &signature);

    let mut signatures = FxHashMap::default();
    signatures.insert(function_name, signature);

    let mut result = InferenceResult { signatures, expr_types, local_types };
    result.shrink_to_fit();

    (result, diagnostics)
}

struct FunctionInferenceCtx<'a> {
    expr_types: &'a mut ArenaMap<Idx<hir::Expr>, ResolvedType>,
    local_types: &'a mut ArenaMap<Idx<hir::LocalDef>, ResolvedType>,
    param_types: &'a [ResolvedType],
    bodies: &'a hir::Bodies,
    index: &'a hir::Index,
    world_index: &'a hir::WorldIndex,
    diagnostics: &'a mut Vec<TypeDiagnostic>,
}

impl FunctionInferenceCtx<'_> {
    fn finish(mut self, function_name: hir::Name, signature: &Signature) {
        let function_body = self.bodies.function_body(function_name);
        let actual_return_type = self.infer_expr(function_body);
        self.expect_match(actual_return_type, signature.return_type, function_body);
    }

    fn infer_stmt(&mut self, stmt: Idx<hir::Stmt>) -> Option<ResolvedType> {
        match &self.bodies[stmt] {
            hir::Stmt::Expr(expr) => {
                self.infer_expr(*expr);
                None
            }
            hir::Stmt::LocalDef(local_def) => {
                let def_body = &self.bodies[*local_def];
                let type_ = self.infer_expr(def_body.value);
                
                if let Some((type_annotation, range)) = def_body.type_annotation {
                    let type_annotation = resolve_type(type_annotation, Some(range), self.index, self.diagnostics);
                    self.expect_match(type_, type_annotation, def_body.value);
                }

                self.local_types.insert(*local_def, type_);
                None
            }
        }
    }

    fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedType {
        let type_ = match &self.bodies[expr] {
            hir::Expr::Missing => ResolvedType::Unknown,
            hir::Expr::IntLiteral(_) => ResolvedType::S32,
            hir::Expr::StringLiteral(_) => ResolvedType::String,
            hir::Expr::Binary { lhs, rhs, .. } => {
                let lhs_type = self.infer_expr(*lhs);
                let rhs_type = self.infer_expr(*rhs);

                if self.expect_match(lhs_type, ResolvedType::S32, *lhs) & 
                    self.expect_match(rhs_type, ResolvedType::S32, *rhs) {
                    ResolvedType::S32
                } else {
                    ResolvedType::Unknown
                }
            },
            hir::Expr::Unary { expr, .. } => {
                let expr_type = self.infer_expr(*expr);

                if self.expect_match(expr_type, ResolvedType::S32, *expr) {
                    ResolvedType::S32
                } else {
                    ResolvedType::Unknown
                }
            },
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.infer_stmt(*stmt);
                }

                match tail_expr {
                    Some(tail) => self.infer_expr(*tail),
                    None => ResolvedType::Void,
                }
            },
            hir::Expr::Local(local_def) => self.local_types[*local_def],
            hir::Expr::Param { idx } => self.param_types[*idx as usize],
            hir::Expr::Call { path, args } => {
                let definition = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => {
                        self.index.get_definition(name).unwrap()
                    }
                    hir::PathWithRange::OtherModule { fqn, .. } => {
                        self.world_index.get_definition(fqn).unwrap()
                    }
                };

                let function = match definition {
                    hir::Definition::Function(f) => f,
                    _ => todo!(),
                };

                let signature = get_signature(
                    function,
                    path.path(),
                    self.index,
                    self.world_index,
                    self.diagnostics,
                );

                for (idx, arg) in args.iter().enumerate() {
                    let arg_type = self.infer_expr(*arg);
                    self.expect_match(arg_type, signature.param_types[idx], *arg);
                }

                signature.return_type
            }
            hir::Expr::Global(path) => {
                let (definition, path_range) = match *path {
                    hir::PathWithRange::ThisModule { name, range } => {
                        (self.index.get_definition(name).unwrap(), range)
                    }
                    hir::PathWithRange::OtherModule { fqn, name_range, .. } => {
                        (self.world_index.get_definition(fqn).unwrap(), name_range)
                    }
                };

                let type_ = match definition {
                    hir::Definition::Function(hir::Function { return_type, .. }) => return_type,
                    hir::Definition::Global(hir::Global { type_ }) => type_,
                };

                resolve_type(*type_, Some(path_range), self.index, self.diagnostics)
            },
        };

        self.expr_types.insert(expr, type_);

        type_
    }

    fn expect_match(&mut self, found: ResolvedType, expected: ResolvedType, expr: Idx<hir::Expr>) -> bool {
        if found == ResolvedType::Unknown || expected == ResolvedType::Unknown {
            return true;
        }

        if found != expected {
            // if the erroneous expression is a block with a return expression,
            // attach the error to the return instead of the whole block
            let expr = match self.bodies[expr] {
                hir::Expr::Block { tail_expr: Some(tail_expr), .. } => tail_expr,
                _ => expr,
            };

            self.diagnostics.push(TypeDiagnostic {
                kind: TypeDiagnosticKind::Mismatch { expected, found },
                range: self.bodies.range_for_expr(expr),
            });

            false
        } else {
            true
        }
    }
}

fn get_signature(
    function: &hir::Function,
    path: hir::Path,
    index: &hir::Index,
    world_index: &hir::WorldIndex,
    diagnostics: &mut Vec<TypeDiagnostic>,
) -> Signature {
    let range_info = match path {
        hir::Path::ThisModule(name) => index.range_info(name),
        hir::Path::OtherModule(fqn) => world_index.range_info(fqn),
    };

    let (return_type_range, param_type_ranges) = match &range_info.types {
        hir::TypesRangeInfo::Function { return_type, param_types } => (return_type, param_types),
        _ => unreachable!(),
    };

    let return_type = resolve_type(function.return_type, *return_type_range, index, diagnostics);

    let param_types: Vec<_> = function
        .params
        .iter()
        .zip(param_type_ranges)
        .map(|(param, type_range)| resolve_type(param.type_, *type_range, index, diagnostics))
        .collect();

    Signature { return_type, param_types }
}

fn resolve_type(
    type_: hir::Type,
    range: Option<TextRange>,
    index: &hir::Index,
    diagnostics: &mut Vec<TypeDiagnostic>,
) -> ResolvedType {
    match type_ {
        hir::Type::Unknown => ResolvedType::Unknown,
        hir::Type::S32 => ResolvedType::S32,
        hir::Type::String => ResolvedType::String,
        hir::Type::Named(name) => match index.get_definition(name) {
            Some(definition) => match definition {
                _ => todo!(),
            },
            None => {
                diagnostics.push(TypeDiagnostic {
                    kind: TypeDiagnosticKind::Undefined { name: name.0 },
                    range: range.unwrap(),
                });
                ResolvedType::Unknown
            }
        },
        hir::Type::Void => ResolvedType::Void,
    }
}

impl InferenceResult {
    fn shrink_to_fit(&mut self) {
        let Self { signatures, expr_types, local_types } = self;
        signatures.shrink_to_fit();
        // expr_types.shrink_to_fit();
        // local_types.shrink_to_fit();
    }
}

impl InferenceResult {
    pub fn debug(&self, interner: &Interner) -> String {
        let mut s = String::new();

        for (name, signature) in &self.signatures {
            s.push_str(&format!("{} = (", interner.lookup(name.0)));
            for (idx, param_type) in signature.param_types.iter().enumerate() {
                if idx != 0 {
                    s.push_str(", ");
                }
                s.push_str(&param_type.display(interner));
            }
            s.push(')');

            s.push_str(&format!(" -> {}\n", signature.return_type.display(interner)));
        }

        s.push('\n');
        for (expr_idx, type_) in self.expr_types.iter() {
            s.push_str(&format!("{}: {}\n", expr_idx.into_raw(), type_.display(interner)));
        }

        if self.local_types.iter().next().is_none() {
            return s;
        }

        s.push('\n');
        for (local_def_idx, type_) in self.local_types.iter() {
            s.push_str(&format!("l{}: {}\n", local_def_idx.into_raw(), type_.display(interner)));
        }

        s
    }
}

impl ResolvedType {
    pub fn display(self, interner: &Interner) -> String {
        match self {
            Self::Unknown => "<unknown>".to_string(),
            Self::S32 => "s32".to_string(),
            Self::String => "string".to_string(),
            Self::Named(fqn) => {
                format!("{}.{}", interner.lookup(fqn.module.0), interner.lookup(fqn.name.0))
            }
            Self::Void => "void".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::AstNode;
    use expect_test::{expect, Expect};
    use hir::WorldIndex;
    use interner::Interner;

    #[track_caller]
    fn check<const N: usize>(
        input: &str,
        function_name: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(&mut Interner) -> [(TypeDiagnosticKind, std::ops::Range<u32>); N],
    ) {
        let modules = test_utils::split_multi_module_test_data(input);
        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        for (name, text) in &modules {
            if *name == "main" {
                continue;
            }

            let tokens = lexer::lex(text);
            let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, _) = hir::index(root, &tree, &mut interner);

            world_index.add_module(hir::Name(interner.intern(name)), index);
        }

        let text = &modules["main"];
        let tokens = lexer::lex(text);
        let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut interner);
        let (bodies, _) = hir::lower(root, &tree, &index, &world_index, &mut interner);

        let (inference_result, actual_diagnostics) =
            infer(hir::Name(interner.intern(function_name)), &bodies, &index, &world_index);

        expect.assert_eq(&inference_result.debug(&interner));

        let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
            .into_iter()
            .map(|(kind, range)| TypeDiagnostic {
                kind,
                range: TextRange::new(range.start.into(), range.end.into()),
            })
            .collect();

        assert_eq!(expected_diagnostics, actual_diagnostics);
    }

    #[test]
    fn unit_function() {
        check(
            r#"
                foo = () {};
            "#,
            "foo",
            expect![[r#"
                foo = () -> void

                0: void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn function_with_return_ty() {
        check(
            r#"
                one = () -> s32 { 1 };
            "#,
            "one",
            expect![[r#"
                one = () -> s32

                0: s32
                1: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn functions_with_undefined_return_ty() {
        check(
            r#"
                one = () -> foo {};
                two = () -> bar.baz {};
            "#,
            "one",
            expect![[r#"
                one = () -> <unknown>

                0: void
            "#]],
            |i| {
                [
                    (TypeDiagnosticKind::Undefined { name: i.intern("foo") }, 29..32),
                ]
            },
        );
    }

    #[test]
    fn binary_expr() {
        check(
            r#"
                twenty = () -> s32 { 10 + 10 };
            "#,
            "twenty",
            expect![[r#"
                twenty = () -> s32

                0: s32
                1: s32
                2: s32
                3: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn function_with_params() {
        check(
            r#"
                add = (x: s32, y: s32) -> s32 { x + y };
            "#,
            "add",
            expect![[r#"
                add = (s32, s32) -> s32

                0: s32
                1: s32
                2: s32
                3: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_definition_and_usage() {
        check(
            r#"
                main = () {
                    a = 10;
                    a;
                };
            "#,
            "main",
            expect![[r#"
                main = () -> void

                0: s32
                1: s32
                2: void

                l0: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_shadowing() {
        check(
            r#"
                foo = () {
                    a = 10;
                    a = "10";
                    a;
                };
            "#,
            "foo",
            expect![[r#"
                foo = () -> void

                0: s32
                1: string
                2: string
                3: void

                l0: s32
                l1: string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn non_s32_binary_expr() {
        check(
            r#"
                sum = () -> s32 { "foo" + 1 };
            "#,
            "sum",
            expect![[r#"
                sum = () -> s32

                0: string
                1: s32
                2: <unknown>
                3: <unknown>
            "#]],
            |_| {
                [(
                    TypeDiagnosticKind::Mismatch {
                        expected: ResolvedType::S32,
                        found: ResolvedType::String,
                    },
                    35..40,
                )]
            },
        );
    }

    #[test]
    fn binary_expr_with_missing_operand() {
        check(
            r#"
                f = () -> s32 { 5 + };
            "#,
            "f",
            expect![[r#"
                f = () -> s32

                0: s32
                1: <unknown>
                2: s32
                3: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_function_body() {
        check(
            r#"
                s = () -> string { 92 };
            "#,
            "s",
            expect![[r#"
                s = () -> string

                0: s32
                1: s32
            "#]],
            |_| {
                [(
                    TypeDiagnosticKind::Mismatch {
                        expected: ResolvedType::String,
                        found: ResolvedType::S32,
                    },
                    36..38,
                )]
            },
        );
    }

    #[test]
    fn call_void_function() {
        check(
            r#"
                main = () { nothing(); };
                nothing = () {};
            "#,
            "main",
            expect![[r#"
                main = () -> void

                0: void
                1: void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn call_function_with_return_ty() {
        check(
            r#"
                main = () -> s32 { number() };
                number = () -> s32 { 5 };
            "#,
            "main",
            expect![[r#"
                main = () -> s32

                0: s32
                1: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn call_function_with_params() {
        check(
            r#"
                main = () -> s32 { id(10) };
                id = (n: s32) -> s32 { n };
            "#,
            "main",
            expect![[r#"
                main = () -> s32

                0: s32
                1: s32
                2: s32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_param_tys() {
        check(
            r#"
                main = () -> s32 { multiply({}, "a") };
                multiply = (x: s32, y: s32) -> s32 { x * y };
            "#,
            "main",
            expect![[r#"
                main = () -> s32

                0: void
                1: string
                2: s32
                3: s32
            "#]],
            |_| {
                [
                    (
                        TypeDiagnosticKind::Mismatch {
                            expected: ResolvedType::S32,
                            found: ResolvedType::Void,
                        },
                        45..47,
                    ),
                    (
                        TypeDiagnosticKind::Mismatch {
                            expected: ResolvedType::S32,
                            found: ResolvedType::String,
                        },
                        49..52,
                    ),
                ]
            },
        );
    }

    #[test]
    fn call_function_from_other_module() {
        check(
            r#"
                #- main
                a = () -> string { greetings.informal(10) };
                #- greetings
                informal = (n: s32) -> string { "Hello!" };
            "#,
            "a",
            expect![[r#"
                a = () -> string

                0: s32
                1: string
                2: string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn attach_mismatch_diagnostics_to_block_tail_expr() {
        check(
            r#"
                main = () {
                    take_s32({
                        a = 10 + 10;
                        "foo"
                    });
                };

                take_s32 = (n: s32) {};
            "#,
            "main",
            expect![[r#"
                main = () -> void

                0: s32
                1: s32
                2: s32
                3: string
                4: string
                5: void
                6: void

                l0: s32
            "#]],
            |_| {
                [(
                    TypeDiagnosticKind::Mismatch {
                        expected: ResolvedType::S32,
                        found: ResolvedType::String,
                    },
                    121..126,
                )]
            },
        );
    }
}
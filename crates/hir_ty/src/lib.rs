mod cast;
mod ctx;

use ctx::InferenceCtx;
use interner::{Interner, Key};
use la_arena::{ArenaMap, Idx};
use rustc_hash::FxHashMap;
use text_size::TextRange;

#[derive(Clone)]
pub struct InferenceResult {
    signatures: FxHashMap<hir::Fqn, Signature>,
    expr_types: ArenaMap<Idx<hir::Expr>, ResolvedTy>,
    local_types: ArenaMap<Idx<hir::LocalDef>, ResolvedTy>,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum ResolvedTy {
    Unknown,
    /// a bit-width of u32::MAX represents an isize
    /// a bit-width of 0 represents ANY signed integer type
    IInt(u32),
    /// a bit-width of u32::MAX represents a usize
    /// a bit-width of 0 represents ANY unsigned integer type
    UInt(u32),
    Bool,
    String,
    Array {
        size: u32,
        sub_ty: Box<ResolvedTy>,
    },
    Named(hir::Fqn),
    Void,
}

impl std::ops::Index<Idx<hir::Expr>> for InferenceResult {
    type Output = ResolvedTy;

    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        &self.expr_types[expr]
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for InferenceResult {
    type Output = ResolvedTy;

    fn index(&self, local_def: Idx<hir::LocalDef>) -> &Self::Output {
        &self.local_types[local_def]
    }
}

#[derive(Debug, Clone)]
enum Signature {
    Function {
        return_type: ResolvedTy,
        param_types: Vec<ResolvedTy>,
    },
    Global(ResolvedTy),
}

impl Signature {
    pub(crate) fn as_function(&self) -> Option<(&ResolvedTy, &Vec<ResolvedTy>)> {
        match self {
            Signature::Function {
                return_type,
                param_types,
            } => Some((return_type, param_types)),
            Signature::Global(_) => None,
        }
    }

    pub(crate) fn as_global(&self) -> Option<&ResolvedTy> {
        match self {
            Signature::Function { .. } => None,
            Signature::Global(type_) => Some(type_),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TyDiagnostic {
    pub kind: TyDiagnosticKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyDiagnosticKind {
    Mismatch {
        expected: ResolvedTy,
        found: ResolvedTy,
    },
    Uncastable {
        from: ResolvedTy,
        to: ResolvedTy,
    },
    OpMismatch {
        op: hir::BinaryOp,
        first: ResolvedTy,
        second: ResolvedTy,
    },
    IfMismatch {
        found: ResolvedTy,
        expected: ResolvedTy,
    },
    MissingElse {
        expected: ResolvedTy,
    },
    Undefined {
        name: Key,
    },
}

pub fn infer_all(
    bodies: &hir::Bodies,
    module: hir::Name,
    world_index: &hir::WorldIndex,
) -> (InferenceResult, Vec<TyDiagnostic>) {
    let index = world_index
        .get_module(module)
        .expect("you must add this module to the world index");
    let mut expr_types = ArenaMap::default();
    let mut local_types = ArenaMap::default();
    let mut diagnostics = Vec::new();
    let mut signatures = FxHashMap::default();

    for (name, global) in index.globals() {
        let global_type = signatures
            .entry(hir::Fqn { module, name })
            .or_insert(get_global_signature(
                global,
                module,
                world_index,
                &mut diagnostics,
            ))
            .as_global()
            .unwrap()
            .clone();

        InferenceCtx {
            expr_tys: &mut expr_types,
            local_tys: &mut local_types,
            param_tys: &[],
            bodies,
            module,
            world_index,
            diagnostics: &mut diagnostics,
            signatures: &mut signatures,
        }
        .finish(bodies.global(name), &global_type);
    }

    for (name, function) in index.functions() {
        let (return_type, param_types) = signatures
            .entry(hir::Fqn { module, name })
            .or_insert_with(|| get_fn_signature(function, module, world_index, &mut diagnostics))
            .as_function()
            .map(|(a, b)| (a.clone(), b.clone()))
            .unwrap();

        InferenceCtx {
            expr_tys: &mut expr_types,
            local_tys: &mut local_types,
            param_tys: &param_types,
            bodies,
            world_index,
            module,
            diagnostics: &mut diagnostics,
            signatures: &mut signatures,
        }
        .finish(bodies.function_body(name), &return_type);
    }

    let mut result = InferenceResult {
        signatures,
        expr_types,
        local_types,
    };
    result.shrink_to_fit();

    (result, diagnostics)
}

pub fn infer(
    fn_name: hir::Fqn,
    bodies: &hir::Bodies,
    world_index: &hir::WorldIndex,
) -> (InferenceResult, Vec<TyDiagnostic>) {
    let function = match world_index.get_definition(fn_name) {
        Ok(hir::Definition::Function(f)) => f,
        Ok(_) | Err(_) => panic!("passed non-function for inference"),
    };

    let mut expr_types = ArenaMap::default();
    let mut local_types = ArenaMap::default();
    let mut diagnostics = Vec::new();

    let mut signatures = FxHashMap::default();

    let (return_type, param_types) = signatures
        .entry(fn_name)
        .or_insert(get_fn_signature(
            function,
            fn_name.module,
            world_index,
            &mut diagnostics,
        ))
        .as_function()
        .map(|(a, b)| (a.clone(), b.clone()))
        .unwrap();

    InferenceCtx {
        expr_tys: &mut expr_types,
        local_tys: &mut local_types,
        param_tys: &param_types,
        bodies,
        module: fn_name.module,
        world_index,
        diagnostics: &mut diagnostics,
        signatures: &mut signatures,
    }
    .finish(bodies.function_body(fn_name.name), &return_type);

    let mut result = InferenceResult {
        signatures,
        expr_types,
        local_types,
    };
    result.shrink_to_fit();

    (result, diagnostics)
}

fn get_global_signature(
    global: &hir::Global,
    module: hir::Name,
    world_index: &hir::WorldIndex,
    diagnostics: &mut Vec<TyDiagnostic>,
) -> Signature {
    Signature::Global(resolve_type(
        global.ty.clone(),
        module,
        world_index,
        diagnostics,
    ))
}

fn get_fn_signature(
    function: &hir::Function,
    module: hir::Name,
    world_index: &hir::WorldIndex,
    diagnostics: &mut Vec<TyDiagnostic>,
) -> Signature {
    let return_type = resolve_type(function.return_ty.clone(), module, world_index, diagnostics);

    let param_types: Vec<_> = function
        .params
        .iter()
        .map(|param| resolve_type(param.ty.clone(), module, world_index, diagnostics))
        .collect();

    Signature::Function {
        return_type,
        param_types,
    }
}

fn resolve_type(
    ty: hir::TyWithRange,
    module: hir::Name,
    world_index: &hir::WorldIndex,
    diagnostics: &mut Vec<TyDiagnostic>,
) -> ResolvedTy {
    match ty {
        hir::TyWithRange::Unknown => ResolvedTy::Unknown,
        hir::TyWithRange::IInt { bit_width, .. } => ResolvedTy::IInt(bit_width),
        hir::TyWithRange::UInt { bit_width, .. } => ResolvedTy::UInt(bit_width),
        hir::TyWithRange::Bool { .. } => ResolvedTy::Bool,
        hir::TyWithRange::String { .. } => ResolvedTy::String,
        hir::TyWithRange::Array { size, sub_ty, .. } => ResolvedTy::Array {
            size,
            sub_ty: Box::new(resolve_type(*sub_ty, module, world_index, diagnostics)),
        },
        hir::TyWithRange::Named { name, range } => {
            match world_index.get_definition(hir::Fqn { module, name }) {
                Ok(definition) => match definition {
                    _ => todo!(),
                },
                Err(_) => {
                    diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::Undefined { name: name.0 },
                        range,
                    });
                    ResolvedTy::Unknown
                }
            }
        }
        hir::TyWithRange::Void { .. } => ResolvedTy::Void,
    }
}

impl InferenceResult {
    fn shrink_to_fit(&mut self) {
        let Self { signatures, .. } = self;
        signatures.shrink_to_fit();
        // expr_types.shrink_to_fit();
        // local_types.shrink_to_fit();
    }
}

impl InferenceResult {
    pub fn debug(&self, interner: &Interner) -> String {
        let mut s = String::new();

        for (name, signature) in &self.signatures {
            match signature {
                Signature::Function {
                    return_type,
                    param_types,
                } => {
                    s.push_str(&format!(
                        "{}.{} : (",
                        interner.lookup(name.module.0),
                        interner.lookup(name.name.0)
                    ));
                    for (idx, param_type) in param_types.iter().enumerate() {
                        if idx != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&param_type.display(interner));
                    }
                    s.push(')');

                    s.push_str(&format!(" -> {}\n", return_type.display(interner)));
                }
                Signature::Global(type_) => {
                    s.push_str(&format!(
                        "{}.{} : ",
                        interner.lookup(name.module.0),
                        interner.lookup(name.name.0)
                    ));
                    s.push_str(&format!("{}\n", type_.display(interner)));
                }
            }
        }

        for (expr_idx, type_) in self.expr_types.iter() {
            s.push_str(&format!(
                "{} : {}\n",
                expr_idx.into_raw(),
                type_.display(interner)
            ));
        }

        for (local_def_idx, type_) in self.local_types.iter() {
            s.push_str(&format!(
                "l{} : {}\n",
                local_def_idx.into_raw(),
                type_.display(interner)
            ));
        }

        s
    }
}

impl ResolvedTy {
    pub fn display(&self, interner: &Interner) -> String {
        match self {
            Self::Unknown => "<unknown>".to_string(),
            Self::IInt(bit_width) => match *bit_width {
                u32::MAX => "isize".to_string(),
                0 => "{int}".to_string(),
                _ => format!("i{}", bit_width),
            },
            Self::UInt(bit_width) => match *bit_width {
                u32::MAX => "usize".to_string(),
                0 => "{uint}".to_string(),
                _ => format!("u{}", bit_width),
            },
            Self::Bool => "bool".to_string(),
            Self::String => "string".to_string(),
            Self::Array { size, sub_ty } => {
                format!("[{size}]{}", sub_ty.display(interner))
            }
            Self::Named(fqn) => {
                format!(
                    "{}.{}",
                    interner.lookup(fqn.module.0),
                    interner.lookup(fqn.name.0)
                )
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
    use interner::Interner;

    #[track_caller]
    fn check<const N: usize>(
        input: &str,
        function_name: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(&mut Interner) -> [(TyDiagnosticKind, std::ops::Range<u32>); N],
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
        let module = hir::Name(interner.intern("main"));
        let tokens = lexer::lex(text);
        let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut interner);
        world_index.add_module(module, index);

        let (bodies, _) = hir::lower(root, &tree, module, &world_index, &mut interner);

        let (inference_result, actual_diagnostics) = infer(
            hir::Fqn {
                module,
                name: hir::Name(interner.intern(function_name)),
            },
            &bodies,
            &world_index,
        );

        expect.assert_eq(&inference_result.debug(&interner));

        let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
            .into_iter()
            .map(|(kind, range)| TyDiagnostic {
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
                foo := () -> {};
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> void
                0 : void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn function_with_return_ty() {
        check(
            r#"
                one := () -> i32 { 1 };
            "#,
            "one",
            expect![[r#"
                main.one : () -> i32
                0 : i32
                1 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn functions_with_undefined_return_ty() {
        check(
            r#"
                one := () -> foo {};
                two := () -> bar.baz {};
            "#,
            "one", // `main.two` doesn't appear as it's not referenced by `main.one`
            expect![[r#"
                main.one : () -> <unknown>
                0 : void
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Undefined {
                        name: i.intern("foo"),
                    },
                    30..33,
                )]
            },
        );
    }

    #[test]
    fn binary_expr() {
        check(
            r#"
                twenty := () -> u8 { 10 + 10 };
            "#,
            "twenty",
            expect![[r#"
                main.twenty : () -> u8
                0 : u8
                1 : u8
                2 : u8
                3 : u8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_diff_types() {
        check(
            r#"
                calc := () -> isize {
                    num1 := 4 as i128;
                    num2 := 8 as u16;
                    num1 + num2
                };
            "#,
            "calc",
            expect![[r#"
                main.calc : () -> isize
                0 : i128
                1 : i128
                2 : u16
                3 : u16
                4 : i128
                5 : u16
                6 : i128
                7 : i128
                l0 : i128
                l1 : u16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_uint_type() {
        check(
            r#"
                calc := () -> u128 {
                    num1 := 4 as u16;
                    num1 + 8
                };
            "#,
            "calc",
            expect![[r#"
                main.calc : () -> u128
                0 : u16
                1 : u16
                2 : u16
                3 : {uint}
                4 : u16
                5 : u16
                l0 : u16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_int_type() {
        check(
            r#"
                calc := () -> i128 {
                    num1: u16 = 4;
                    num1 + -8
                };
            "#,
            "calc",
            expect![[r#"
                main.calc : () -> i128
                0 : u16
                1 : u16
                2 : i128
                3 : i128
                4 : i128
                5 : i128
                l0 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::UInt(16),
                        second: ResolvedTy::IInt(0),
                    },
                    93..102,
                )]
            },
        );
    }

    #[test]
    fn cast() {
        check(
            r#"
                check := () -> bool {
                    num := 5;
                    is_true := num as bool;
                    is_true
                };
            "#,
            "check",
            expect![[r#"
                main.check : () -> bool
                0 : {uint}
                1 : {uint}
                2 : bool
                3 : bool
                4 : bool
                l0 : {uint}
                l1 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cast_unrelated() {
        check(
            r#"
                how_old := () -> usize {
                    name := "Gandalf";
                    age := name as usize;
                    age
                };
            "#,
            "how_old",
            expect![[r#"
                main.how_old : () -> usize
                0 : string
                1 : string
                2 : usize
                3 : usize
                4 : usize
                l0 : string
                l1 : usize
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: ResolvedTy::String,
                        to: ResolvedTy::UInt(u32::MAX),
                    },
                    108..121,
                )]
            },
        );
    }

    #[test]
    fn inference_simple_by_annotation() {
        check(
            r#"
                main := () -> {
                    num1 := 5;
                    num2 := num1;
                    num3 : usize = num2;
                };
            "#,
            "main",
            expect![[r#"
                main.main : () -> void
                0 : usize
                1 : usize
                2 : usize
                3 : void
                l0 : usize
                l1 : usize
                l2 : usize
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_complex_by_annotation() {
        check(
            r#"
                main := () -> {
                    num: i16 = {
                        res := 23;
                        if true {
                            res
                        } else {
                            -42
                        }
                    };
                };
            "#,
            "main",
            expect![[r#"
                main.main : () -> void
                0 : i16
                1 : bool
                2 : i16
                3 : i16
                4 : i16
                5 : i16
                6 : i16
                7 : i16
                8 : i16
                9 : void
                l0 : i16
                l1 : i16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_simple_by_return() {
        check(
            r#"
                main := () -> usize {
                    num1 := 5;
                    num2 := num1;
                    num2
                };
            "#,
            "main",
            expect![[r#"
                main.main : () -> usize
                0 : usize
                1 : usize
                2 : usize
                3 : usize
                l0 : usize
                l1 : usize
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_complex_by_return_ok() {
        check(
            r#"
                main := () -> i8 {
                    num := {
                        res := 23;
                        if true {
                            res
                        } else {
                            -42
                        }
                    };
                    num
                };
            "#,
            "main",
            expect![[r#"
                main.main : () -> i8
                0 : i8
                1 : bool
                2 : i8
                3 : i8
                4 : i8
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : i8
                l0 : i8
                l1 : i8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_complex_by_return_err() {
        check(
            r#"
                main := () -> u8 {
                    num := {
                        res := 23;
                        if true {
                            res
                        } else {
                            -42
                        }
                    };
                    num
                };
            "#,
            "main",
            expect![[r#"
                main.main : () -> u8
                0 : u8
                1 : bool
                2 : u8
                3 : u8
                4 : u8
                5 : u8
                6 : u8
                7 : u8
                8 : u8
                9 : u8
                10 : u8
                l0 : u8
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::IInt(0),
                    },
                    300..303,
                )]
            },
        );
    }

    #[test]
    fn function_with_params() {
        check(
            r#"
                add := (x: i32, y: i32) -> i32 { x + y };
            "#,
            "add",
            expect![[r#"
                main.add : (i32, i32) -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_definition_and_usage() {
        check(
            r#"
                main := () -> {
                    a := 10;
                    a;
                };
            "#,
            "main",
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : void
                l0 : {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_shadowing() {
        check(
            r#"
                foo := () -> {
                    a := 10;
                    a := "10";
                    a;
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> void
                0 : {uint}
                1 : string
                2 : string
                3 : void
                l0 : {uint}
                l1 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_set() {
        check(
            r#"
                foo := () -> {
                    a := "Hello";
                    a = "World";
                    a;
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> void
                0 : string
                1 : string
                2 : string
                3 : void
                l0 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_auto_small_to_big_same_sign() {
        check(
            r#"
                foo := () -> i16 {
                    small: i8 = 42;
                    big: i16 = small;
                    big
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> i16
                0 : i8
                1 : i8
                2 : i16
                3 : i16
                l0 : i8
                l1 : i16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_auto_big_to_small_same_sign() {
        check(
            r#"
                foo := () -> u8 {
                    big: u16 = 42;
                    small: u8 = big;
                    small
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> u8
                0 : u16
                1 : u16
                2 : u8
                3 : u8
                l0 : u16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::UInt(16),
                    },
                    102..105,
                )]
            },
        );
    }

    #[test]
    fn local_auto_small_unsign_to_big_sign() {
        check(
            r#"
                foo := () -> i16 {
                    small: u8 = 42;
                    big: i16 = small;
                    big
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> i16
                0 : u8
                1 : u8
                2 : i16
                3 : i16
                l0 : u8
                l1 : i16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_auto_small_sign_to_big_unsign() {
        check(
            r#"
                foo := () -> u16 {
                    small: i8 = 42;
                    big: u16 = small;
                    big
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> u16
                0 : i8
                1 : i8
                2 : u16
                3 : u16
                l0 : i8
                l1 : u16
            "#]],
            |_| {
                // should fail due to loss of sign
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(16),
                        found: ResolvedTy::IInt(8),
                    },
                    103..108,
                )]
            },
        );
    }

    #[test]
    fn local_auto_sign_to_unsign() {
        check(
            r#"
                foo := () -> u16 {
                    sign: i16 = 42;
                    nada: u16 = sign;
                    nada
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> u16
                0 : i16
                1 : i16
                2 : u16
                3 : u16
                l0 : i16
                l1 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(16),
                        found: ResolvedTy::IInt(16),
                    },
                    104..108,
                )]
            },
        );
    }

    #[test]
    fn local_auto_big_sign_to_small_unsign() {
        check(
            r#"
                foo := () -> u8 {
                    big: i16 = 42;
                    small: u8 = big;
                    small
                };
            "#,
            "foo",
            expect![[r#"
                main.foo : () -> u8
                0 : i16
                1 : i16
                2 : u8
                3 : u8
                l0 : i16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::IInt(16),
                    },
                    102..105,
                )]
            },
        );
    }

    #[test]
    fn non_int_binary_expr() {
        check(
            r#"
                sum := () -> i32 { "foo" + 1 };
            "#,
            "sum",
            expect![[r#"
                main.sum : () -> i32
                0 : string
                1 : i32
                2 : i32
                3 : i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::String,
                        second: ResolvedTy::UInt(0),
                    },
                    36..45,
                )]
            },
        );
    }

    #[test]
    fn binary_expr_with_missing_operand() {
        check(
            r#"
                f := () -> i32 { 5 + };
            "#,
            "f",
            expect![[r#"
                main.f : () -> i32
                0 : i32
                1 : <unknown>
                2 : i32
                3 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn invalid_binary_expr_with_missing_operand() {
        check(
            r#"
                f := () -> string { "hello" + };
            "#,
            "f",
            expect![[r#"
                main.f : () -> string
                0 : string
                1 : <unknown>
                2 : string
                3 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn invalid_num_cmp_binary_expr() {
        check(
            r#"
                f := () -> bool { true < 5 };
            "#,
            "f",
            expect![[r#"
                main.f : () -> bool
                0 : bool
                1 : {uint}
                2 : bool
                3 : bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Lt,
                        first: ResolvedTy::Bool,
                        second: ResolvedTy::UInt(0),
                    },
                    35..43,
                )]
            },
        );
    }

    #[test]
    fn invalid_bool_cmp_binary_expr() {
        check(
            r#"
                f := () -> bool { "hello" && "world" };
            "#,
            "f",
            expect![[r#"
                main.f : () -> bool
                0 : string
                1 : string
                2 : bool
                3 : bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::And,
                        first: ResolvedTy::String,
                        second: ResolvedTy::String,
                    },
                    35..53,
                )]
            },
        );
    }

    #[test]
    fn bool_binary_expr() {
        check(
            r#"
                both := () -> bool { true && false };
            "#,
            "both",
            expect![[r#"
                main.both : () -> bool
                0 : bool
                1 : bool
                2 : bool
                3 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn bool_binary_expr_with_missing_operand() {
        check(
            r#"
                either := () -> bool { true || };
            "#,
            "either",
            expect![[r#"
                main.either : () -> bool
                0 : bool
                1 : <unknown>
                2 : bool
                3 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cmp_binary_expr() {
        check(
            r#"
                less := () -> bool { 5 <= 10 };
            "#,
            "less",
            expect![[r#"
                main.less : () -> bool
                0 : {uint}
                1 : {uint}
                2 : bool
                3 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cmp_binary_expr_with_missing_operands() {
        check(
            r#"
                equality := () -> bool { 42 == };
            "#,
            "equality",
            expect![[r#"
                main.equality : () -> bool
                0 : {uint}
                1 : <unknown>
                2 : bool
                3 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn pos_unary_expr() {
        check(
            r#"
                redundant := () -> u8 { +4 };
            "#,
            "redundant",
            expect![[r#"
                main.redundant : () -> u8
                0 : u8
                1 : u8
                2 : u8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn neg_unary_expr() {
        check(
            r#"
                neg := () -> u8 { -4 };
            "#,
            "neg",
            expect![[r#"
                main.neg : () -> u8
                0 : u8
                1 : u8
                2 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::IInt(0),
                    },
                    35..37,
                )]
            },
        );
    }

    #[test]
    fn multi_neg_unary_expr() {
        check(
            r#"
                pos := () -> u8 { ----4 };
            "#,
            "pos",
            expect![[r#"
                main.pos : () -> u8
                0 : u8
                1 : u8
                2 : u8
                3 : u8
                4 : u8
                5 : u8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn bang_unary_expr() {
        check(
            r#"
                not := () -> bool { !true };
            "#,
            "not",
            expect![[r#"
                main.not : () -> bool
                0 : bool
                1 : bool
                2 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_function_body() {
        check(
            r#"
                s := () -> string { 92 };
            "#,
            "s",
            expect![[r#"
                main.s : () -> string
                0 : {uint}
                1 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::String,
                        found: ResolvedTy::UInt(0),
                    },
                    37..39,
                )]
            },
        );
    }

    #[test]
    fn call_void_function() {
        check(
            r#"
                main := () -> { nothing(); };
                nothing := () -> {};
            "#,
            "main",
            expect![[r#"
                main.main : () -> void
                main.nothing : () -> void
                0 : void
                1 : void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn call_function_with_return_ty() {
        check(
            r#"
                main := () -> i32 { number() };
                number := () -> i32 { 5 };
            "#,
            "main",
            expect![[r#"
                main.main : () -> i32
                main.number : () -> i32
                0 : i32
                1 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn call_function_with_params() {
        check(
            r#"
                main := () -> i32 { id(10) };
                id := (n: i32) -> i32 { n };
            "#,
            "main",
            expect![[r#"
                main.main : () -> i32
                main.id : (i32) -> i32
                0 : i32
                1 : i32
                2 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_param_tys() {
        check(
            r#"
                main := () -> i32 { multiply({}, "a") };
                multiply := (x: i32, y: i32) -> i32 { x * y };
            "#,
            "main", // `main` references `multiply`, so it shows up here
            expect![[r#"
                main.main : () -> i32
                main.multiply : (i32, i32) -> i32
                0 : void
                1 : string
                2 : i32
                3 : i32
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::IInt(32),
                            found: ResolvedTy::Void,
                        },
                        46..48,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::IInt(32),
                            found: ResolvedTy::String,
                        },
                        50..53,
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
                a := () -> string { greetings.informal(10) };
                #- greetings
                informal := (n: i32) -> string { "Hello!" };
            "#,
            "a",
            expect![[r#"
                main.a : () -> string
                greetings.informal : (i32) -> string
                0 : i32
                1 : string
                2 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn attach_mismatch_diagnostics_to_block_tail_expr() {
        check(
            r#"
                main := () -> {
                    take_i32({
                        a := 10 + 10;
                        "foo"
                    });
                };

                take_i32 := (n: i32) {};
            "#,
            "main",
            expect![[r#"
                main.main : () -> void
                main.take_i32 : (i32) -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : string
                4 : string
                5 : void
                6 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::IInt(32),
                        found: ResolvedTy::String,
                    },
                    126..131,
                )]
            },
        );
    }
}

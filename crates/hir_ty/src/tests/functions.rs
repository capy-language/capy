use super::*;

use expect_test::expect;
use la_arena::RawIdx;

#[test]
fn unit_function() {
    check(
        r#"
            foo :: () {};
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              1 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : void
              1 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn function_with_return_ty() {
    check(
        r#"
            one :: () -> i32 { 1 };
        "#,
        expect![[r#"
            main::one : main::one() -> i32
              3 : main::one() -> i32
            main::lambda#one : main::one() -> i32
              1 : i32
              2 : i32
              3 : main::one() -> i32
        "#]],
        |_| [],
    );
}

#[test]
fn function_with_float_return_ty() {
    check(
        r#"
            one :: () -> f32 { 1.0 };
        "#,
        expect![[r#"
            main::one : main::one() -> f32
              3 : main::one() -> f32
            main::lambda#one : main::one() -> f32
              1 : f32
              2 : f32
              3 : main::one() -> f32
        "#]],
        |_| [],
    );
}

#[test]
fn function_with_float_return_ty_int_body() {
    check(
        r#"
            one :: () -> f32 { 1 };
        "#,
        expect![[r#"
            main::one : main::one() -> f32
              3 : main::one() -> f32
            main::lambda#one : main::one() -> f32
              1 : f32
              2 : f32
              3 : main::one() -> f32
        "#]],
        |_| [],
    );
}

#[test]
fn function_with_params() {
    check(
        r#"
            add :: (x: i32, y: i32) -> i32 { x + y };
        "#,
        expect![[r#"
            main::add : main::add(i32, i32) -> i32
              7 : main::add(i32, i32) -> i32
            main::lambda#add : main::add(i32, i32) -> i32
              3 : i32
              4 : i32
              5 : i32
              6 : i32
              7 : main::add(i32, i32) -> i32
        "#]],
        |_| [],
    );
}

#[test]
fn mismatched_function_body() {
    check(
        r#"
            s :: () -> str { 92 };
        "#,
        expect![[r#"
            main::s : main::s() -> str
              3 : main::s() -> str
            main::lambda#s : main::s() -> str
              1 : {uint}
              2 : <unknown>
              3 : main::s() -> str
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::String.into()),
                    found: Ty::UInt(0).into(),
                },
                30..32,
                Some((
                    TyDiagnosticHelpKind::ReturnTyHere {
                        ty: Ty::String.into(),
                        is_default: false,
                    },
                    24..27,
                )),
            )]
        },
    );
}

#[test]
fn call_void_function() {
    check(
        r#"
            main :: () { nothing(); };
            nothing :: () {};
        "#,
        expect![[r#"
            main::main : main::main() -> void
              3 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : main::nothing() -> void
              1 : void
              2 : void
              3 : main::main() -> void
            main::nothing : main::nothing() -> void
              5 : main::nothing() -> void
            main::lambda#nothing : main::nothing() -> void
              4 : void
              5 : main::nothing() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn call_function_with_return_ty() {
    check(
        r#"
            main :: () -> i32 { number() };
            number :: () -> i32 { 5 };
        "#,
        expect![[r#"
            main::main : main::main() -> i32
              4 : main::main() -> i32
            main::lambda#main : main::main() -> i32
              1 : main::number() -> i32
              2 : i32
              3 : i32
              4 : main::main() -> i32
            main::number : main::number() -> i32
              8 : main::number() -> i32
            main::lambda#number : main::number() -> i32
              6 : i32
              7 : i32
              8 : main::number() -> i32
        "#]],
        |_| [],
    );
}

#[test]
fn call_function_with_params() {
    check(
        r#"
            main :: () -> i32 { id(10) };
            id :: (n: i32) -> i32 { n };
        "#,
        expect![[r#"
            main::main : main::main() -> i32
              5 : main::main() -> i32
            main::lambda#main : main::main() -> i32
              1 : main::id(i32) -> i32
              2 : i32
              3 : i32
              4 : i32
              5 : main::main() -> i32
            main::id : main::id(i32) -> i32
              10 : main::id(i32) -> i32
            main::lambda#id : main::id(i32) -> i32
              8 : i32
              9 : i32
              10 : main::id(i32) -> i32
        "#]],
        |_| [],
    );
}

#[test]
fn mismatched_param_tys() {
    check(
        r#"
            main :: () -> i32 { multiply({}, "a") };
            multiply :: (x: i32, y: i32) -> i32 { x * y };
        "#,
        expect![[r#"
            main::main : main::main() -> i32
              6 : main::main() -> i32
            main::lambda#main : main::main() -> i32
              1 : main::multiply(i32, i32) -> i32
              2 : void
              3 : str
              4 : i32
              5 : i32
              6 : main::main() -> i32
            main::multiply : main::multiply(i32, i32) -> i32
              14 : main::multiply(i32, i32) -> i32
            main::lambda#multiply : main::multiply(i32, i32) -> i32
              10 : i32
              11 : i32
              12 : i32
              13 : i32
              14 : main::multiply(i32, i32) -> i32
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::Void.into(),
                    },
                    42..44,
                    None,
                ),
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::String.into(),
                    },
                    46..49,
                    None,
                ),
            ]
        },
    );
}

#[test]
fn call_function_from_other_file() {
    check(
        r#"
            #- main.capy
            a :: () -> str {
                greetings := #import("greetings.capy");

                greetings.informal(10)
            };
            #- greetings.capy
            informal :: (n: i32) -> str { "Hello!" };
        "#,
        expect![[r#"
            greetings::informal : greetings::informal(i32) -> str
              4 : greetings::informal(i32) -> str
            greetings::lambda#informal : greetings::informal(i32) -> str
              2 : str
              3 : str
              4 : greetings::informal(i32) -> str
            main::a : main::a() -> str
              7 : main::a() -> str
            main::lambda#a : main::a() -> str
              1 : file greetings
              2 : file greetings
              3 : greetings::informal(i32) -> str
              4 : i32
              5 : str
              6 : str
              7 : main::a() -> str
              l0 : file greetings
        "#]],
        |_| [],
    );
}

#[test]
fn attach_mismatch_diagnostics_to_block_tail_expr() {
    check(
        r#"
            main :: () {
                take_i32({
                    a := 10 + 10;
                    "foo"
                });
            };

            take_i32 :: (n: i32) {};
        "#,
        expect![[r#"
            main::main : main::main() -> void
              8 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : main::take_i32(i32) -> void
              1 : {uint}
              2 : {uint}
              3 : {uint}
              4 : str
              5 : str
              6 : void
              7 : void
              8 : main::main() -> void
              l0 : {uint}
            main::take_i32 : main::take_i32(i32) -> void
              11 : main::take_i32(i32) -> void
            main::lambda#take_i32 : main::take_i32(i32) -> void
              10 : void
              11 : main::take_i32(i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                    found: Ty::String.into(),
                },
                51..130,
                Some((TyDiagnosticHelpKind::TailExprReturnsHere, 107..112)),
            )]
        },
    );
}

#[test]
fn fn_with_ty_annotation_ok() {
    check(
        r#"
            foo : (arg: i32) -> void : (x: i32) {
                // do stuff
            };
        "#,
        expect![[r#"
            main::foo : (i32) -> void
              5 : main::foo(i32) -> void
            main::lambda#foo : main::foo(i32) -> void
              4 : void
              5 : main::foo(i32) -> void
        "#]],
        |_| [],
    );
}

#[test]
fn fn_with_diff_fn_annotation() {
    check(
        r#"
            foo : (arg: f32, arg2: i8) -> str : (x: i32) {
                foo(x);
            };
        "#,
        expect![[r#"
            main::foo : (f32, i8) -> str
              9 : main::foo(i32) -> void
            main::lambda#foo : main::foo(i32) -> void
              5 : (f32, i8) -> str
              6 : i32
              7 : str
              8 : void
              9 : main::foo(i32) -> void
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::FunctionPointer {
                                param_tys: vec![
                                    ParamTy {
                                        ty: Ty::Float(32).into(),
                                        comptime: None,
                                        varargs: false,
                                        impossible_to_differentiate: false,
                                    },
                                    ParamTy {
                                        ty: Ty::IInt(8).into(),
                                        comptime: None,
                                        varargs: false,
                                        impossible_to_differentiate: false,
                                    },
                                ],
                                return_ty: Ty::String.into(),
                            }
                            .into(),
                        ),
                        found: Ty::ConcreteFunction {
                            param_tys: vec![ParamTy {
                                ty: Ty::IInt(32).into(),
                                comptime: None,
                                varargs: false,
                                impossible_to_differentiate: false,
                            }],
                            return_ty: Ty::Void.into(),
                            fn_loc: NaiveLambdaLoc {
                                file: FileName(i.intern("main.capy")),
                                expr: Idx::<hir::Expr>::from_raw(RawIdx::from_u32(9)),
                                lambda: Idx::<hir::Lambda>::from_raw(RawIdx::from_u32(1)),
                            }
                            .make_concrete(None),
                        }
                        .into(),
                    },
                    49..97,
                    None,
                ),
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Float(32).into()),
                        found: Ty::IInt(32).into(),
                    },
                    80..81,
                    None,
                ),
                (
                    TyDiagnosticKind::MissingArg {
                        expected: ExpectedTy::Concrete(Ty::IInt(8).into()),
                    },
                    81..81,
                    None,
                ),
            ]
        },
    );
}

#[test]
fn fn_with_comptime_param_ty_annotation_no_initial_call() {
    // this is empty because generic functions aren't type checked until someone calls them.
    // TODO: change this behavior, make it so generic functions are type checked once and then
    // the generic types are just "filled in"
    check(
        r#"
            foo : (arg: f32, comptime arg2: i8, arg3: bool) -> str :
            (arg: f32, comptime arg2: i8, arg3: bool) -> str {
                "Hello, World!"
            }
        "#,
        expect![[r#"
"#]],
        |_| [],
    );
}

#[test]
fn fn_with_comptime_param_ty_annotation_with_initial_call() {
    // this is empty because generic functions aren't type checked until someone calls them.
    // TODO: change this behavior, make it so generic functions are type checked once and then
    // the generic types are just "filled in"
    check(
        r#"
            foo : (arg: f32, comptime arg2: i8, arg3: bool) -> str :
            (arg: f32, comptime arg2: i8, arg3: bool) -> str {
                "Hello, World!"
            }

            main :: () {
                foo(2.5, 1, true);
            }
        "#,
        expect![[r#"
            main::foo<0> : <unknown>
              11 : main::foo<0>(f32, i8, bool) -> str
            main::lambda#foo<0> : main::foo<0>(f32, i8, bool) -> str
              9 : str
              10 : str
              11 : main::foo<0>(f32, i8, bool) -> str
            main::main : main::main() -> void
              18 : main::main() -> void
            main::lambda#main : main::main() -> void
              12 : main::foo<?>
              13 : {float}
              14 : i8
              15 : bool
              16 : <unknown>
              17 : void
              18 : main::main() -> void
"#]],
        |_| {
            [(
                TyDiagnosticKind::FunctionTypeWithComptimeParameters,
                19..67,
                None,
            )]
        },
    );
}

#[test]
fn fn_with_global_annotation() {
    // todo: it should print the annotationhere help diag
    check(
        r#"
            foo : i32 : (x: i32) {
                foo(x);
            }
        "#,
        expect![[r#"
            main::foo : i32
              6 : main::foo(i32) -> void
            main::lambda#foo : main::foo(i32) -> void
              2 : i32
              3 : i32
              4 : <unknown>
              5 : void
              6 : main::foo(i32) -> void
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::ConcreteFunction {
                            param_tys: vec![ParamTy {
                                ty: Ty::IInt(32).into(),
                                comptime: None,
                                varargs: false,
                                impossible_to_differentiate: false,
                            }],
                            return_ty: Ty::Void.into(),
                            fn_loc: NaiveLambdaLoc {
                                file: FileName(i.intern("main.capy")),
                                expr: Idx::<hir::Expr>::from_raw(RawIdx::from_u32(6)),
                                lambda: Idx::<hir::Lambda>::from_raw(RawIdx::from_u32(0)),
                            }
                            .make_concrete(None),
                        }
                        .into(),
                    },
                    25..73,
                    None,
                ),
                (
                    TyDiagnosticKind::CalledNonFunction {
                        found: Ty::IInt(32).into(),
                    },
                    52..58,
                    None,
                ),
            ]
        },
    );
}

#[test]
fn fn_ty() {
    check(
        r#"
            foo :: () {
                Fn_Type :: (x: str, y: bool, z: char) -> void;
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              4 : type
              5 : void
              6 : main::foo() -> void
              l0 : type
        "#]],
        |_| [],
    );
}

#[test]
fn fn_ty_comptime_param() {
    check(
        r#"
            foo :: () {
                Fn_Type :: (x: str, comptime y: bool, z: char) -> void;
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              4 : <unknown>
              5 : void
              6 : main::foo() -> void
              l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::FunctionTypeWithComptimeParameters,
                52..95,
                None,
            )]
        },
    );
}

#[test]
fn extra_arg() {
    // todo: since there are two extra args here, maybe throw two errors instead of one
    check(
        r#"
            bar :: (num: i32) {};

            foo :: () {
                bar(1, 2, 3);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(i32) -> void
              2 : main::bar(i32) -> void
            main::lambda#bar : main::bar(i32) -> void
              1 : void
              2 : main::bar(i32) -> void
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : main::bar(i32) -> void
              4 : i32
              5 : {uint}
              6 : {uint}
              7 : void
              8 : void
              9 : main::foo() -> void
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::UInt(0).into(),
                    },
                    83..84,
                    None,
                ),
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::UInt(0).into(),
                    },
                    86..87,
                    None,
                ),
            ]
        },
    );
}

#[test]
fn missing_arg() {
    check(
        r#"
            bar :: (num: i32, text: str, condition: bool) {};

            foo :: () {
                bar(1, "hello");
            }
        "#,
        expect![[r#"
            main::bar : main::bar(i32, str, bool) -> void
              4 : main::bar(i32, str, bool) -> void
            main::lambda#bar : main::bar(i32, str, bool) -> void
              3 : void
              4 : main::bar(i32, str, bool) -> void
            main::foo : main::foo() -> void
              10 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              5 : main::bar(i32, str, bool) -> void
              6 : i32
              7 : str
              8 : void
              9 : void
              10 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MissingArg {
                    expected: ExpectedTy::Concrete(Ty::Bool.into()),
                },
                118..118,
                None,
            )]
        },
    );
}

#[test]
fn varargs() {
    check(
        r#"
            bar :: (numbers: ...i8) {};

            foo :: () {
                bar(1, 2, 3, 4, 5);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8) -> void
              2 : main::bar(...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8) -> void
              1 : void
              2 : main::bar(...[]i8) -> void
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : main::bar(...[]i8) -> void
              4 : i8
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : void
              10 : void
              11 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn varargs_trailing_comma() {
    check(
        r#"
            bar :: (numbers: ...i8) {};

            foo :: () {
                bar(1, 2, 3, 4, 5,);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8) -> void
              2 : main::bar(...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8) -> void
              1 : void
              2 : main::bar(...[]i8) -> void
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : main::bar(...[]i8) -> void
              4 : i8
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : void
              10 : void
              11 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn multiple_varargs() {
    check(
        r#"
            bar :: (numbers: ...i8, conditions: ...bool, text: ...str, more_numbers: ...i8) {};

            foo :: () {
                bar(1, 2, 3, 4, 5, true, false, "hello", "world", "sailor", "wassup", 42);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
              5 : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
              4 : void
              5 : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            main::foo : main::foo() -> void
              21 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              6 : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
              7 : i8
              8 : i8
              9 : i8
              10 : i8
              11 : i8
              12 : bool
              13 : bool
              14 : str
              15 : str
              16 : str
              17 : str
              18 : i8
              19 : void
              20 : void
              21 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn multiple_varargs_with_regular_args() {
    check(
        r#"
            bar :: (numbers: ...i8, a: str, conditions: ...bool, b: str, text: ...str, c: i8, more_numbers: ...i8) {};

            foo :: () {
                bar(1, 2, 3, 4, 5, "conditions: ", true, false, "text: ", "hello", "world", "sailor", "wassup", 0, 42);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
              8 : main::bar(...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
              7 : void
              8 : main::bar(...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
            main::foo : main::foo() -> void
              27 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              9 : main::bar(...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
              10 : i8
              11 : i8
              12 : i8
              13 : i8
              14 : i8
              15 : str
              16 : bool
              17 : bool
              18 : str
              19 : str
              20 : str
              21 : str
              22 : str
              23 : i8
              24 : i8
              25 : void
              26 : void
              27 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn empty_varargs() {
    check(
        r#"
            bar :: (conditions: ...bool) {};

            foo :: () {
                bar();
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]bool) -> void
              2 : main::bar(...[]bool) -> void
            main::lambda#bar : main::bar(...[]bool) -> void
              1 : void
              2 : main::bar(...[]bool) -> void
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : main::bar(...[]bool) -> void
              4 : void
              5 : void
              6 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn multiple_empty_varargs() {
    check(
        r#"
            bar :: (numbers: ...i8, conditions: ...bool, text: ...str, more_numbers: ...i8) {};

            foo :: () {
                bar();
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
              5 : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
              4 : void
              5 : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              6 : main::bar(...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
              7 : void
              8 : void
              9 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn multiple_empty_varargs_one_regular_arg_diff_than_previous() {
    check(
        r#"
            bar :: (numbers: ...i8, conditions: ...bool, regular_arg: str, text: ...str, more_numbers: ...i8) {};

            foo :: () {
                bar("will this go to the regular arg?");
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
              6 : main::bar(...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
              5 : void
              6 : main::bar(...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : main::bar(...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
              8 : str
              9 : void
              10 : void
              11 : main::foo() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn multiple_empty_varargs_one_regular_arg_same_as_previous() {
    // todo: this is kind of ambiguous
    check(
        r#"
            bar :: (numbers: ...i8, conditions: ...bool, regular_arg: i64, text: ...str, more_numbers: ...i8) {};

            foo :: () {
                bar(42);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
              6 : main::bar(...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
            main::lambda#bar : main::bar(...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
              5 : void
              6 : main::bar(...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : main::bar(...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
              8 : i8
              9 : void
              10 : void
              11 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MissingArg {
                    expected: ExpectedTy::Concrete(Ty::IInt(64).into()),
                },
                162..162,
                None,
            )]
        },
    );
}

#[test]
fn impossible_to_differentiate_prev_varargs_next_arg() {
    check(
        r#"
            bar :: (first: ...i8, second: i64) {};

            foo :: () {
                bar(1, 2, 3, 4, 5);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, i64) -> void
              3 : main::bar(...[]i8, i64) -> void
            main::lambda#bar : main::bar(...[]i8, i64) -> void
              2 : void
              3 : main::bar(...[]i8, i64) -> void
            main::foo : main::foo() -> void
              12 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              4 : main::bar(...[]i8, i64) -> void
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : i8
              10 : void
              11 : void
              12 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                    previous_ty: Ty::IInt(8).into(),
                    current_ty: Ty::IInt(64).into(),
                },
                35..46,
                None,
            )]
        },
    );
}

#[test]
fn impossible_to_differentiate_prev_varargs_next_vararg() {
    check(
        r#"
            bar :: (first: ...i8, second: ...u64) {};

            foo :: () {
                bar(1, 2, 3, 4, 5);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, ...[]u64) -> void
              3 : main::bar(...[]i8, ...[]u64) -> void
            main::lambda#bar : main::bar(...[]i8, ...[]u64) -> void
              2 : void
              3 : main::bar(...[]i8, ...[]u64) -> void
            main::foo : main::foo() -> void
              12 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              4 : main::bar(...[]i8, ...[]u64) -> void
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : i8
              10 : void
              11 : void
              12 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                    previous_ty: Ty::IInt(8).into(),
                    current_ty: Ty::UInt(64).into(),
                },
                35..49,
                None,
            )]
        },
    );
}

#[test]
fn impossible_to_differentiate_prev_varargs_next_any_vararg() {
    check(
        r#"
            bar :: (first: ...i8, second: ...any) {};

            foo :: () {
                bar(1, 2, 3, 4, 5);
            }
        "#,
        expect![[r#"
            main::bar : main::bar(...[]i8, ...[]any) -> void
              3 : main::bar(...[]i8, ...[]any) -> void
            main::lambda#bar : main::bar(...[]i8, ...[]any) -> void
              2 : void
              3 : main::bar(...[]i8, ...[]any) -> void
            main::foo : main::foo() -> void
              12 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              4 : main::bar(...[]i8, ...[]any) -> void
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : i8
              10 : void
              11 : void
              12 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                    previous_ty: Ty::IInt(8).into(),
                    current_ty: Ty::Any.into(),
                },
                35..49,
                None,
            )]
        },
    );
}

#[test]
fn call_non_function() {
    // todo: the range should be on `wow` and not on the entire call
    check(
        r#"
            foo :: () {
                wow := "Wow!";

                wow(42);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              5 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              1 : str
              2 : {uint}
              3 : <unknown>
              4 : void
              5 : main::foo() -> void
              l0 : str
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CalledNonFunction {
                    found: Ty::String.into(),
                },
                73..80,
                None,
            )]
        },
    );
}

#[test]
fn param_as_ty() {
    check(
        r#"
            foo :: (T: type) {
                wow : T = "hello :)";
            }
        "#,
        expect![[r#"
            main::foo : main::foo(type) -> void
              4 : main::foo(type) -> void
            main::lambda#foo : main::foo(type) -> void
              2 : str
              3 : void
              4 : main::foo(type) -> void
              l0 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::ParamNotATy, 54..55, None)],
    );
}

use super::*;

use expect_test::expect;

#[test]
fn unit_function() {
    check(
        r#"
            foo :: () {};
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : void
            1 : () -> void
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
            main::one : () -> i32
            1 : i32
            2 : i32
            3 : () -> i32
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
            main::one : () -> f32
            1 : f32
            2 : f32
            3 : () -> f32
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
            main::one : () -> f32
            1 : f32
            2 : f32
            3 : () -> f32
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
            main::add : (i32, i32) -> i32
            3 : i32
            4 : i32
            5 : i32
            6 : i32
            7 : (i32, i32) -> i32
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
            main::s : () -> str
            1 : {uint}
            2 : <unknown>
            3 : () -> str
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
            main::main : () -> void
            main::nothing : () -> void
            0 : () -> void
            1 : void
            2 : void
            3 : () -> void
            4 : void
            5 : () -> void
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
            main::main : () -> i32
            main::number : () -> i32
            1 : () -> i32
            2 : i32
            3 : i32
            4 : () -> i32
            6 : i32
            7 : i32
            8 : () -> i32
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
            main::id : (i32) -> i32
            main::main : () -> i32
            1 : (i32) -> i32
            2 : i32
            3 : i32
            4 : i32
            5 : () -> i32
            8 : i32
            9 : i32
            10 : (i32) -> i32
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
            main::main : () -> i32
            main::multiply : (i32, i32) -> i32
            1 : (i32, i32) -> i32
            2 : void
            3 : str
            4 : i32
            5 : i32
            6 : () -> i32
            10 : i32
            11 : i32
            12 : i32
            13 : i32
            14 : (i32, i32) -> i32
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
            greetings::informal : (i32) -> str
            main::a : () -> str
            greetings:
              2 : str
              3 : str
              4 : (i32) -> str
            main:
              1 : file greetings
              2 : file greetings
              3 : (i32) -> str
              4 : i32
              5 : str
              6 : str
              7 : () -> str
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
            main::main : () -> void
            main::take_i32 : (i32) -> void
            0 : (i32) -> void
            1 : {uint}
            2 : {uint}
            3 : {uint}
            4 : str
            5 : str
            6 : void
            7 : void
            8 : () -> void
            10 : void
            11 : (i32) -> void
            l0 : {uint}
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
            4 : void
            5 : (i32) -> void
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
            5 : (f32, i8) -> str
            6 : i32
            7 : str
            8 : void
            9 : (i32) -> void
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Function {
                                param_tys: vec![
                                    ParamTy {
                                        ty: Ty::Float(32).into(),
                                        varargs: false,
                                        impossible_to_differentiate: false,
                                    },
                                    ParamTy {
                                        ty: Ty::IInt(8).into(),
                                        varargs: false,
                                        impossible_to_differentiate: false,
                                    },
                                ],
                                return_ty: Ty::String.into(),
                            }
                            .into(),
                        ),
                        found: Ty::Function {
                            param_tys: vec![ParamTy {
                                ty: Ty::IInt(32).into(),
                                varargs: false,
                                impossible_to_differentiate: false,
                            }],
                            return_ty: Ty::Void.into(),
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
            2 : i32
            3 : i32
            4 : <unknown>
            5 : void
            6 : (i32) -> void
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::Function {
                            param_tys: vec![ParamTy {
                                ty: Ty::IInt(32).into(),
                                varargs: false,
                                impossible_to_differentiate: false,
                            }],
                            return_ty: Ty::Void.into(),
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
            main::bar : (i32) -> void
            main::foo : () -> void
            1 : void
            2 : (i32) -> void
            3 : (i32) -> void
            4 : i32
            5 : {uint}
            6 : {uint}
            7 : void
            8 : void
            9 : () -> void
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
            main::bar : (i32, str, bool) -> void
            main::foo : () -> void
            3 : void
            4 : (i32, str, bool) -> void
            5 : (i32, str, bool) -> void
            6 : i32
            7 : str
            8 : void
            9 : void
            10 : () -> void
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
            main::bar : (...[]i8) -> void
            main::foo : () -> void
            1 : void
            2 : (...[]i8) -> void
            3 : (...[]i8) -> void
            4 : i8
            5 : i8
            6 : i8
            7 : i8
            8 : i8
            9 : void
            10 : void
            11 : () -> void
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
            main::bar : (...[]i8) -> void
            main::foo : () -> void
            1 : void
            2 : (...[]i8) -> void
            3 : (...[]i8) -> void
            4 : i8
            5 : i8
            6 : i8
            7 : i8
            8 : i8
            9 : void
            10 : void
            11 : () -> void
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
            main::bar : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            main::foo : () -> void
            4 : void
            5 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            6 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
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
            21 : () -> void
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
            main::bar : (...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
            main::foo : () -> void
            7 : void
            8 : (...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
            9 : (...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
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
            27 : () -> void
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
            main::bar : (...[]bool) -> void
            main::foo : () -> void
            1 : void
            2 : (...[]bool) -> void
            3 : (...[]bool) -> void
            4 : void
            5 : void
            6 : () -> void
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
            main::bar : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            main::foo : () -> void
            4 : void
            5 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            6 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
            7 : void
            8 : void
            9 : () -> void
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
            main::bar : (...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
            main::foo : () -> void
            5 : void
            6 : (...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
            7 : (...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
            8 : str
            9 : void
            10 : void
            11 : () -> void
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
            main::bar : (...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
            main::foo : () -> void
            5 : void
            6 : (...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
            7 : (...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
            8 : i8
            9 : void
            10 : void
            11 : () -> void
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
            main::bar : (...[]i8, i64) -> void
            main::foo : () -> void
            2 : void
            3 : (...[]i8, i64) -> void
            4 : (...[]i8, i64) -> void
            5 : i8
            6 : i8
            7 : i8
            8 : i8
            9 : i8
            10 : void
            11 : void
            12 : () -> void
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
            main::bar : (...[]i8, ...[]u64) -> void
            main::foo : () -> void
            2 : void
            3 : (...[]i8, ...[]u64) -> void
            4 : (...[]i8, ...[]u64) -> void
            5 : i8
            6 : i8
            7 : i8
            8 : i8
            9 : i8
            10 : void
            11 : void
            12 : () -> void
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
            main::bar : (...[]i8, ...[]any) -> void
            main::foo : () -> void
            2 : void
            3 : (...[]i8, ...[]any) -> void
            4 : (...[]i8, ...[]any) -> void
            5 : i8
            6 : i8
            7 : i8
            8 : i8
            9 : i8
            10 : void
            11 : void
            12 : () -> void
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
            main::foo : () -> void
            0 : str
            1 : str
            2 : {uint}
            3 : <unknown>
            4 : void
            5 : () -> void
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
            main::foo : (type) -> void
            2 : str
            3 : void
            4 : (type) -> void
            l0 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::ParamNotATy, 54..55, None)],
    );
}

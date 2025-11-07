use super::*;

use expect_test::expect;

#[test]
fn distinct_int_mismatch() {
    check(
        r#"
            imaginary : type : distinct i32;

            main :: () -> i32 {
                i : imaginary = 1;

                i
            };
        "#,
        expect![[r#"
            main::imaginary : type
              2 : type
            main::main : main::main() -> i32
              8 : main::main() -> i32
            main::lambda#main : main::main() -> i32
              5 : main::imaginary
              6 : main::imaginary
              7 : <unknown>
              8 : main::main() -> i32
              l0 : main::imaginary
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                    found: Ty::Distinct {
                        uid: 0,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                },
                131..132,
                Some((
                    TyDiagnosticHelpKind::ReturnTyHere {
                        ty: Ty::IInt(32).into(),
                        is_default: false,
                    },
                    73..76,
                )),
            )]
        },
    );
}

#[test]
fn distinct_int_binary_weak_int() {
    check(
        r#"
            imaginary : type : distinct i32;

            main :: () -> imaginary {
                i : imaginary = 1;

                i + 2
            };
        "#,
        expect![[r#"
            main::imaginary : type
              2 : type
            main::main : main::main() -> main::imaginary
              10 : main::main() -> main::imaginary
            main::lambda#main : main::main() -> main::imaginary
              5 : main::imaginary
              6 : main::imaginary
              7 : main::imaginary
              8 : main::imaginary
              9 : main::imaginary
              10 : main::main() -> main::imaginary
              l0 : main::imaginary
        "#]],
        |_| [],
    );
}

#[test]
fn distinct_int_binary_itself() {
    check(
        r#"
            imaginary : type : distinct i32;

            main :: () -> imaginary {
                i : imaginary = 1;

                i + i
            };
        "#,
        expect![[r#"
            main::imaginary : type
              2 : type
            main::main : main::main() -> main::imaginary
              10 : main::main() -> main::imaginary
            main::lambda#main : main::main() -> main::imaginary
              5 : main::imaginary
              6 : main::imaginary
              7 : main::imaginary
              8 : main::imaginary
              9 : main::imaginary
              10 : main::main() -> main::imaginary
              l0 : main::imaginary
        "#]],
        |_| [],
    );
}

#[test]
fn distinct_int_binary_strong_int() {
    check(
        r#"
            imaginary : type : distinct i32;

            main :: () -> imaginary {
                i : imaginary = 1;
                x : i32 = 1;

                i + x
            };
        "#,
        expect![[r#"
            main::imaginary : type
              2 : type
            main::main : main::main() -> main::imaginary
              12 : main::main() -> main::imaginary
            main::lambda#main : main::main() -> main::imaginary
              5 : main::imaginary
              7 : i32
              8 : main::imaginary
              9 : i32
              10 : main::imaginary
              11 : main::imaginary
              12 : main::main() -> main::imaginary
              l0 : main::imaginary
              l1 : i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Add,
                    first: Ty::Distinct {
                        uid: 0,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                    second: Ty::IInt(32).into(),
                },
                166..171,
                None,
            )]
        },
    );
}

#[test]
fn distinct_int_binary_other_distinct() {
    check(
        r#"
            imaginary : type : distinct i32;
            extra_imaginary : type : distinct i32;

            main :: () -> imaginary {
                i : imaginary = 1;
                x : extra_imaginary = 1;

                i + x
            };
        "#,
        expect![[r#"
            main::imaginary : type
              2 : type
            main::extra_imaginary : type
              5 : type
            main::main : main::main() -> main::imaginary
              15 : main::main() -> main::imaginary
            main::lambda#main : main::main() -> main::imaginary
              8 : main::imaginary
              10 : main::extra_imaginary
              11 : main::imaginary
              12 : main::extra_imaginary
              13 : main::imaginary
              14 : main::imaginary
              15 : main::main() -> main::imaginary
              l0 : main::imaginary
              l1 : main::extra_imaginary
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Add,
                    first: Ty::Distinct {
                        uid: 0,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                    second: Ty::Distinct {
                        uid: 1,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                },
                229..234,
                None,
            )]
        },
    );
}

#[test]
fn distinct_pointers() {
    check(
        r#"
            something_far_away :: distinct ^i32;

            main :: () -> i32 {
                i : something_far_away = ^1;

                ^i32.(i)^
            };
        "#,
        expect![[r#"
            main::something_far_away : type
              2 : type
            main::main : main::main() -> i32
              13 : main::main() -> i32
            main::lambda#main : main::main() -> i32
              5 : i32
              6 : ^i32
              7 : main::something_far_away
              10 : ^i32
              11 : i32
              12 : i32
              13 : main::main() -> i32
              l0 : main::something_far_away
        "#]],
        |_| [],
    );
}

#[test]
fn distinct_pointers_to_distinct_tys() {
    check(
        r#"
            imaginary :: distinct i32;
            imaginary_far_away :: distinct ^imaginary;

            main :: () -> imaginary {
                i : imaginary = 1;

                x : imaginary_far_away = ^i;

                ^imaginary.(x)^
            };
        "#,
        expect![[r#"
            main::imaginary : type
              1 : type
            main::imaginary_far_away : type
              4 : type
            main::main : main::main() -> main::imaginary
              17 : main::main() -> main::imaginary
            main::lambda#main : main::main() -> main::imaginary
              7 : main::imaginary
              9 : main::imaginary
              10 : ^main::imaginary
              11 : main::imaginary_far_away
              14 : ^main::imaginary
              15 : main::imaginary
              16 : main::imaginary
              17 : main::main() -> main::imaginary
              l0 : main::imaginary
              l1 : main::imaginary_far_away
        "#]],
        |_| [],
    );
}

#[test]
fn distinct_arrays() {
    check(
        r#"
            Vector3 :: distinct [3] i32;

            main :: () {
                my_point : Vector3 = i32.[4, 8, 15];

                x := my_point[0];
                y := my_point[1];
                z := my_point[2];
            };
        "#,
        expect![[r#"
            main::Vector3 : type
              0 : usize
              3 : type
            main::main : main::main() -> void
              20 : main::main() -> void
            main::lambda#main : main::main() -> void
              6 : i32
              7 : i32
              8 : i32
              9 : [3]i32
              10 : main::Vector3
              11 : usize
              12 : i32
              13 : main::Vector3
              14 : usize
              15 : i32
              16 : main::Vector3
              17 : usize
              18 : i32
              19 : void
              20 : main::main() -> void
              l0 : main::Vector3
              l1 : i32
              l2 : i32
              l3 : i32
        "#]],
        |_| [],
    );
}

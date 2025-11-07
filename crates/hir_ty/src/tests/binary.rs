use super::*;

use expect_test::expect;

#[test]
fn binary_expr() {
    check(
        r#"
            twenty :: () -> u8 { 10 + 10 };
        "#,
        expect![[r#"
            main::twenty : main::twenty() -> u8
              5 : main::twenty() -> u8
            main::lambda#twenty : main::twenty() -> u8
              1 : u8
              2 : u8
              3 : u8
              4 : u8
              5 : main::twenty() -> u8
        "#]],
        |_| [],
    );
}

#[test]
fn binary_expr_diff_types() {
    check(
        r#"
            calc :: () -> isize {
                num1 := i128.(4);
                num2 := u16.(8);
                num1 + num2
            };
        "#,
        expect![[r#"
            main::calc : main::calc() -> isize
              11 : main::calc() -> isize
            main::lambda#calc : main::calc() -> isize
              1 : i128
              3 : i128
              4 : u16
              6 : u16
              7 : i128
              8 : u16
              9 : i128
              10 : isize
              11 : main::calc() -> isize
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
            calc :: () -> u128 {
                num1 := u16.(4);
                num1 + 8
            };
        "#,
        expect![[r#"
            main::calc : main::calc() -> u128
              8 : main::calc() -> u128
            main::lambda#calc : main::calc() -> u128
              1 : u16
              3 : u16
              4 : u16
              5 : u16
              6 : u16
              7 : u128
              8 : main::calc() -> u128
              l0 : u16
        "#]],
        |_| [],
    );
}

#[test]
fn binary_expr_weak_int_type() {
    check(
        r#"
            calc :: () -> i128 {
                num1: u16 = 4;
                num1 + -8
            };
        "#,
        expect![[r#"
            main::calc : main::calc() -> i128
              8 : main::calc() -> i128
            main::lambda#calc : main::calc() -> i128
              2 : u16
              3 : u16
              4 : i128
              5 : i128
              6 : i128
              7 : i128
              8 : main::calc() -> i128
              l0 : u16
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Add,
                    first: Ty::UInt(16).into(),
                    second: Ty::IInt(0).into(),
                },
                81..90,
                None,
            )]
        },
    );
}

#[test]
fn binary_expr_float_and_float() {
    check(
        r#"
            main :: () {
                foo : f32 = 5;
                bar : f64 = 10;

                foo + bar;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              8 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : f32
              3 : f64
              4 : f32
              5 : f64
              6 : f64
              7 : void
              8 : main::main() -> void
              l0 : f32
              l1 : f64
        "#]],
        |_| [],
    );
}

#[test]
fn binary_expr_strong_int_and_strong_float() {
    check(
        r#"
            main :: () {
                foo : i32 = 5;
                bar : f64 = 10;

                foo + bar;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              8 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : i32
              3 : f64
              4 : i32
              5 : f64
              6 : f64
              7 : void
              8 : main::main() -> void
              l0 : i32
              l1 : f64
        "#]],
        |_| [],
    );
}

#[test]
fn binary_expr_weak_int_and_strong_float() {
    check(
        r#"
            main :: () {
                foo : f64 = 10;

                5 + foo;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              6 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : f64
              2 : f64
              3 : f64
              4 : f64
              5 : void
              6 : main::main() -> void
              l0 : f64
        "#]],
        |_| [],
    );
}

#[test]
fn binary_expr_weak_int_and_weak_float() {
    check(
        r#"
            main :: () {
                5 + 10.0;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              4 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : {float}
              1 : {float}
              2 : {float}
              3 : void
              4 : main::main() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn non_int_binary_expr() {
    check(
        r#"
            sum :: () -> i32 { "foo" + 1 };
        "#,
        expect![[r#"
            main::sum : main::sum() -> i32
              5 : main::sum() -> i32
            main::lambda#sum : main::sum() -> i32
              1 : str
              2 : i32
              3 : i32
              4 : i32
              5 : main::sum() -> i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Add,
                    first: Ty::String.into(),
                    second: Ty::UInt(0).into(),
                },
                32..41,
                None,
            )]
        },
    );
}

#[test]
fn binary_expr_with_missing_operand() {
    check(
        r#"
            f :: () -> i32 { 5 + };
        "#,
        expect![[r#"
            main::f : main::f() -> i32
              5 : main::f() -> i32
            main::lambda#f : main::f() -> i32
              1 : i32
              2 : <unknown>
              3 : i32
              4 : i32
              5 : main::f() -> i32
        "#]],
        |_| [],
    );
}

#[test]
fn invalid_binary_expr_with_missing_operand() {
    check(
        r#"
            f :: () -> str { "hello" + };
        "#,
        expect![[r#"
            main::f : main::f() -> str
              5 : main::f() -> str
            main::lambda#f : main::f() -> str
              1 : str
              2 : <unknown>
              3 : str
              4 : str
              5 : main::f() -> str
        "#]],
        |_| [],
    );
}

#[test]
fn invalid_num_cmp_binary_expr() {
    check(
        r#"
            f :: () -> bool { true < 5 };
        "#,
        expect![[r#"
            main::f : main::f() -> bool
              5 : main::f() -> bool
            main::lambda#f : main::f() -> bool
              1 : bool
              2 : {uint}
              3 : bool
              4 : bool
              5 : main::f() -> bool
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::Lt,
                    first: Ty::Bool.into(),
                    second: Ty::UInt(0).into(),
                },
                31..39,
                None,
            )]
        },
    );
}

#[test]
fn invalid_bool_cmp_binary_expr() {
    check(
        r#"
            f :: () -> bool { "hello" && "world" };
        "#,
        expect![[r#"
            main::f : main::f() -> bool
              5 : main::f() -> bool
            main::lambda#f : main::f() -> bool
              1 : str
              2 : str
              3 : bool
              4 : bool
              5 : main::f() -> bool
        "#]],
        |_| {
            [(
                TyDiagnosticKind::BinaryOpMismatch {
                    op: hir::BinaryOp::LAnd,
                    first: Ty::String.into(),
                    second: Ty::String.into(),
                },
                31..49,
                None,
            )]
        },
    );
}

#[test]
fn bool_binary_expr() {
    check(
        r#"
            both :: () -> bool { true && false };
        "#,
        expect![[r#"
            main::both : main::both() -> bool
              5 : main::both() -> bool
            main::lambda#both : main::both() -> bool
              1 : bool
              2 : bool
              3 : bool
              4 : bool
              5 : main::both() -> bool
        "#]],
        |_| [],
    );
}

#[test]
fn bool_binary_expr_with_missing_operand() {
    check(
        r#"
            either :: () -> bool { true || };
        "#,
        expect![[r#"
            main::either : main::either() -> bool
              5 : main::either() -> bool
            main::lambda#either : main::either() -> bool
              1 : bool
              2 : <unknown>
              3 : bool
              4 : bool
              5 : main::either() -> bool
        "#]],
        |_| [],
    );
}

#[test]
fn cmp_binary_expr() {
    check(
        r#"
            less :: () -> bool { 5 <= 10 };
        "#,
        expect![[r#"
            main::less : main::less() -> bool
              5 : main::less() -> bool
            main::lambda#less : main::less() -> bool
              1 : {uint}
              2 : {uint}
              3 : bool
              4 : bool
              5 : main::less() -> bool
        "#]],
        |_| [],
    );
}

#[test]
fn cmp_binary_expr_with_missing_operands() {
    check(
        r#"
            equality :: () -> bool { 42 == };
        "#,
        expect![[r#"
            main::equality : main::equality() -> bool
              5 : main::equality() -> bool
            main::lambda#equality : main::equality() -> bool
              1 : {uint}
              2 : <unknown>
              3 : bool
              4 : bool
              5 : main::equality() -> bool
        "#]],
        |_| [],
    );
}

#[test]
fn compare_bool_to_bool() {
    check(
        r#"
            foo :: () {
                true == false;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              4 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : bool
              1 : bool
              2 : bool
              3 : void
              4 : main::foo() -> void
        "#]],
        |_| [],
    )
}

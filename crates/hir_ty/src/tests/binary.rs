use super::*;

use expect_test::expect;

#[test]
fn binary_expr() {
    check(
        r#"
            twenty :: () -> u8 { 10 + 10 };
        "#,
        expect![[r#"
            main::twenty : () -> u8
            1 : u8
            2 : u8
            3 : u8
            4 : u8
            5 : () -> u8
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
            main::calc : () -> isize
            1 : i128
            3 : i128
            4 : u16
            6 : u16
            7 : i128
            8 : u16
            9 : i128
            10 : isize
            11 : () -> isize
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
            main::calc : () -> u128
            1 : u16
            3 : u16
            4 : u16
            5 : u16
            6 : u16
            7 : u128
            8 : () -> u128
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
            main::calc : () -> i128
            2 : u16
            3 : u16
            4 : i128
            5 : i128
            6 : i128
            7 : i128
            8 : () -> i128
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
            main::main : () -> void
            1 : f32
            3 : f64
            4 : f32
            5 : f64
            6 : f64
            7 : void
            8 : () -> void
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
            main::main : () -> void
            1 : i32
            3 : f64
            4 : i32
            5 : f64
            6 : f64
            7 : void
            8 : () -> void
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
            main::main : () -> void
            1 : f64
            2 : f64
            3 : f64
            4 : f64
            5 : void
            6 : () -> void
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
            main::main : () -> void
            0 : {float}
            1 : {float}
            2 : {float}
            3 : void
            4 : () -> void
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
            main::sum : () -> i32
            1 : str
            2 : i32
            3 : i32
            4 : i32
            5 : () -> i32
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
            main::f : () -> i32
            1 : i32
            2 : <unknown>
            3 : i32
            4 : i32
            5 : () -> i32
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
            main::f : () -> str
            1 : str
            2 : <unknown>
            3 : str
            4 : str
            5 : () -> str
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
            main::f : () -> bool
            1 : bool
            2 : {uint}
            3 : bool
            4 : bool
            5 : () -> bool
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
            main::f : () -> bool
            1 : str
            2 : str
            3 : bool
            4 : bool
            5 : () -> bool
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
            main::both : () -> bool
            1 : bool
            2 : bool
            3 : bool
            4 : bool
            5 : () -> bool
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
            main::either : () -> bool
            1 : bool
            2 : <unknown>
            3 : bool
            4 : bool
            5 : () -> bool
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
            main::less : () -> bool
            1 : {uint}
            2 : {uint}
            3 : bool
            4 : bool
            5 : () -> bool
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
            main::equality : () -> bool
            1 : {uint}
            2 : <unknown>
            3 : bool
            4 : bool
            5 : () -> bool
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
            main::foo : () -> void
            0 : bool
            1 : bool
            2 : bool
            3 : void
            4 : () -> void
        "#]],
        |_| [],
    )
}

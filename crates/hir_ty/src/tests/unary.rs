use super::*;

use expect_test::expect;

#[test]
fn pos_unary_expr() {
    check(
        r#"
            redundant :: () -> u8 { +4 };
        "#,
        expect![[r#"
            main::redundant : () -> u8
            1 : u8
            2 : u8
            3 : u8
            4 : () -> u8
        "#]],
        |_| [],
    );
}

#[test]
fn neg_unary_expr() {
    check(
        r#"
            neg :: () -> u8 { -4 };
        "#,
        expect![[r#"
            main::neg : () -> u8
            1 : {int}
            2 : {int}
            3 : <unknown>
            4 : () -> u8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                    found: Ty::IInt(0).into(),
                },
                31..33,
                Some((
                    TyDiagnosticHelpKind::ReturnTyHere {
                        ty: Ty::UInt(8).into(),
                        is_default: false,
                    },
                    26..28,
                )),
            )]
        },
    );
}

#[test]
fn multi_neg_unary_expr() {
    check(
        r#"
            pos :: () -> i8 { ----4 };
        "#,
        expect![[r#"
            main::pos : () -> i8
            1 : i8
            2 : i8
            3 : i8
            4 : i8
            5 : i8
            6 : i8
            7 : () -> i8
        "#]],
        |_| [],
    );
}

#[test]
fn bang_unary_expr() {
    check(
        r#"
            not :: () -> bool { !true };
        "#,
        expect![[r#"
            main::not : () -> bool
            1 : bool
            2 : bool
            3 : bool
            4 : () -> bool
        "#]],
        |_| [],
    );
}

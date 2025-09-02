use super::*;

use expect_test::expect;

#[test]
fn int_too_large_for_type() {
    check(
        r#"
            foo :: () {
                my_num : i8 = 128;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : i8
            2 : void
            3 : () -> void
            l0 : i8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IntTooBigForType {
                    found: 128,
                    max: 127,
                    ty: Ty::IInt(8).into(),
                },
                55..58,
                None,
            )]
        },
    );
}

#[test]
fn int_too_large_for_type_by_inference() {
    check(
        r#"
            foo :: () {
                my_num := 128;

                my_other_num : i8 = my_num;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : i8
            2 : i8
            3 : void
            4 : () -> void
            l0 : i8
            l1 : i8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IntTooBigForType {
                    found: 128,
                    max: 127,
                    ty: Ty::IInt(8).into(),
                },
                51..54,
                None,
            )]
        },
    );
}

#[test]
fn inference_by_too_large_for_u32() {
    // todo: why is the type of #0 u64?
    check(
        r#"
            foo :: () {
                my_num := 4_294_967_296;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : u64
            1 : void
            2 : () -> void
            l0 : u64
        "#]],
        |_| [],
    );
}

#[test]
fn inference_by_too_large_for_i32() {
    check(
        r#"
            foo :: () {
                my_num := -2_147_483_648;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : i64
            1 : i64
            2 : void
            3 : () -> void
            l0 : i64
        "#]],
        |_| [],
    );
}

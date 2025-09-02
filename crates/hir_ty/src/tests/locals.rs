use super::*;

use expect_test::expect;

#[test]
fn local_definition_and_usage() {
    check(
        r#"
            main :: () {
                a := 10;
                a;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : void
            3 : () -> void
            l0 : {uint}
        "#]],
        |_| [],
    );
}

#[test]
fn local_shadowing() {
    check(
        r#"
            foo :: () {
                a := 10;
                a := "10";
                a;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : str
            2 : str
            3 : void
            4 : () -> void
            l0 : {uint}
            l1 : str
        "#]],
        |_| [],
    );
}

#[test]
fn assign() {
    check(
        r#"
            foo :: () {
                a := "Hello";
                a = "World"; // `a` on the left is an expression, and it's type is evaluated
                a;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : str
            1 : str
            2 : str
            3 : str
            4 : void
            5 : () -> void
            l0 : str
        "#]],
        |_| [],
    );
}

#[test]
fn local_ty_def() {
    check(
        r#"
            foo :: () {
                imaginary :: distinct i32;

                my_num : imaginary = 5;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : type
            3 : distinct'0 i32
            4 : void
            5 : () -> void
            l0 : type
            l1 : distinct'0 i32
        "#]],
        |_| [],
    );
}

#[test]
fn local_ty_mut() {
    check(
        r#"
            foo :: () {
                imaginary := distinct i32;

                my_num : imaginary = 5;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : type
            3 : {uint}
            4 : void
            5 : () -> void
            l0 : type
            l1 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::LocalTyIsMutable,
                94..103,
                Some((TyDiagnosticHelpKind::MutableVariable, 41..67)),
            )]
        },
    );
}

#[test]
fn local_ty_mut_through_binding() {
    check(
        r#"
            foo :: () {
                imaginary := distinct i32;

                binding :: imaginary;

                my_num : binding = 5;
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : type
            2 : type
            4 : {uint}
            5 : void
            6 : () -> void
            l0 : type
            l1 : type
            l2 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::LocalTyIsMutable,
                96..105,
                Some((TyDiagnosticHelpKind::MutableVariable, 41..67)),
            )]
        },
    );
}

#[test]
fn cast_as_local_ty() {
    check(
        r#"
            foo :: () {
                imaginary :: distinct i32;

                real : i32 = 5;

                imaginary.(real);
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : type
            3 : i32
            4 : i32
            6 : distinct'0 i32
            7 : void
            8 : () -> void
            l0 : type
            l1 : i32
        "#]],
        |_| [],
    );
}

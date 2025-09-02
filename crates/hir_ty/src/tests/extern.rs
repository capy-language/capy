use super::*;

use expect_test::expect;

#[test]
fn extern_function() {
    check(
        r#"
            foo :: (s: str) -> void extern;
        "#,
        expect![[r#"
            main::foo : (str) -> void
            2 : (str) -> void
        "#]],
        |_| [],
    )
}

#[test]
fn extern_global_with_type() {
    check(
        r#"
            foo : i32 : extern;
        "#,
        expect![[r#"
            main::foo : i32
        "#]],
        |_| [],
    )
}

#[test]
fn extern_global_without_type() {
    check(
        r#"
            foo :: extern;
        "#,
        expect![[r#"
            main::foo : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::ExternGlobalMissingTy, 13..27, None)],
    )
}

#[test]
fn extern_global_reference() {
    // mainly just for checking `is_safe_to_compile`
    check(
        r#"
            #- main.capy
            other :: #import("other.capy");

            foo : i32 : extern;

            bar :: () {
                foo;
                other.baz;
            };
            #- other.capy
            baz : i32 : extern;
        "#,
        expect![[r#"
            main::bar : () -> void
            main::foo : i32
            main::other : file other
            other::baz : i32
            other:
            main:
              0 : file other
              2 : i32
              3 : file other
              4 : i32
              5 : void
              6 : () -> void
        "#]],
        |_| [],
    )
}

#[test]
fn extern_varargs() {
    check(
        r#"
            foo :: (s: str, numbers: ...i32) -> void extern;
        "#,
        expect![[r#"
            main::foo : (str, ...[]i32) -> void
            3 : (str, ...[]i32) -> void
        "#]],
        |_| [(TyDiagnosticKind::ExternVarargs, 29..44, None)],
    )
}

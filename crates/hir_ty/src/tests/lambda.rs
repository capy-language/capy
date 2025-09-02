use super::*;

use expect_test::expect;

#[test]
fn lambda_ty_annotation() {
    check(
        r#"
            bar :: (s: str) {
                // do stuff
            } 

            foo :: () {
                a : (s: str) -> void = (s: str) {};

                a = bar;

                a("Hello!");
            }
        "#,
        expect![[r#"
            main::bar : (str) -> void
            main::foo : () -> void
            1 : void
            2 : (str) -> void
            7 : void
            8 : (str) -> void
            9 : (str) -> void
            10 : (str) -> void
            11 : (str) -> void
            12 : str
            13 : void
            14 : void
            15 : () -> void
            l0 : (str) -> void
        "#]],
        |_| [],
    );
}

#[test]
fn lambda_with_body_ty_annotation() {
    // todo: print some help about how the `{}` makes it a lambda and not a function type
    check(
        r#"
            foo :: () {
                a : (s: str) -> void {} = (s: str) {};

                a("Hello!");
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            5 : void
            6 : (str) -> void
            7 : <unknown>
            8 : str
            9 : <unknown>
            10 : void
            11 : () -> void
            l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Type.into()),
                    found: Ty::Function {
                        param_tys: vec![ParamTy {
                            ty: Ty::String.into(),
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::Void.into(),
                    }
                    .into(),
                },
                45..64,
                None,
            )]
        },
    );
}

#[test]
fn lambda_ty_no_return() {
    // this is only to make sure that `is_safe_to_compile` works correctly.
    // this will panic if there's some error and `is_safe_to_compile`
    // returns true. since I know for a fact that the parser is going to throw an
    // error on the following input, and I know that the following did not panic,
    // it's safe to say that `is_safe_to_compile` returned false and
    // works correctly on this input.
    check(
        r#"
            foo :: () {
                (a: i32, b: str);
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            2 : (i32, str) -> void
            3 : void
            4 : () -> void
        "#]],
        |_| [],
    );
}

use super::*;

use expect_test::expect;

#[test]
fn array_of_local_ty() {
    check(
        r#"
            main :: () -> i32 {
                int :: i32;
                imaginary :: distinct int;
                imaginary_vec3 :: distinct [3] imaginary;

                arr : imaginary_vec3 = imaginary.[1, 2, 3];

                i32.(arr[0])
            }
        "#,
        expect![[r#"
            main::main : () -> i32
            1 : type
            3 : type
            4 : usize
            7 : type
            10 : distinct'0 i32
            11 : distinct'0 i32
            12 : distinct'0 i32
            13 : [3]distinct'0 i32
            14 : distinct'1 [3]distinct'0 i32
            15 : usize
            16 : distinct'0 i32
            18 : i32
            19 : i32
            20 : () -> i32
            l0 : type
            l1 : type
            l2 : type
            l3 : distinct'1 [3]distinct'0 i32
        "#]],
        |_| [],
    )
}

#[test]
fn struct_of_local_tys() {
    check(
        r#"
            main :: () -> i32 {
                int :: i32;
                imaginary :: distinct int;
                complex :: struct {
                    real_part: int,
                    imaginary_part: imaginary,
                };

                my_complex := complex.{
                    real_part = 5,
                    imaginary_part = 42,
                };

                i32.(my_complex.real_part) + i32.(my_complex.imaginary_part)
            }
        "#,
        expect![[r#"
            main::main : () -> i32
            1 : type
            3 : type
            6 : type
            8 : i32
            9 : distinct'0 i32
            10 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
            11 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
            12 : i32
            14 : i32
            15 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
            16 : distinct'0 i32
            18 : i32
            19 : i32
            20 : i32
            21 : () -> i32
            l0 : type
            l1 : type
            l2 : type
            l3 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
        "#]],
        |_| [],
    )
}

#[test]
fn lambda_with_local_ty() {
    check(
        r#"
            main :: () -> i32 {
                int :: i32;
                imaginary :: distinct int;
                imaginary_vec3 :: distinct [3] imaginary;
                complex :: struct {
                    real_part: int,
                    imaginary_part: imaginary,
                };
            
                my_complex := complex.{
                    real_part = 5,
                    imaginary_part = 42,
                };
            
                do_math :: (c: complex) -> imaginary_vec3 {
                    // this is kind of akward because while we can access locals
                    // in the parameters and return type, we can't access `imaginary`
                    // from inside the body of this lambda
                    // this could be alleviated by adding a `type_of` builtin
                    i32.[1, c.real_part * i32.(c.imaginary_part), 3]
                };
            
                i32.(do_math(my_complex)[1])
            }
        "#,
        expect![[r#"
            main::main : () -> i32
            1 : type
            3 : type
            4 : usize
            7 : type
            10 : type
            12 : i32
            13 : distinct'0 i32
            14 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
            18 : i32
            19 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
            20 : i32
            21 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
            22 : distinct'0 i32
            24 : i32
            25 : i32
            26 : i32
            27 : [3]i32
            28 : distinct'1 [3]distinct'0 i32
            29 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
            30 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
            31 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
            32 : distinct'1 [3]distinct'0 i32
            33 : usize
            34 : distinct'0 i32
            36 : i32
            37 : i32
            38 : () -> i32
            l0 : type
            l1 : type
            l2 : type
            l3 : type
            l4 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
            l5 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
        "#]],
        |_| [],
    )
}

#[test]
fn ty_ptr_becomes_ty() {
    check(
        r#"
            foo :: () {
                x : type = ^i32;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : type
            2 : type
            3 : void
            4 : () -> void
            l0 : type
        "#]],
        |_| [],
    )
}

#[test]
fn array_literal_as_type() {
    // pre 2/6/2025:
    // this is just to make sure that the compiler doens't show a diagnostic
    // like "expected `type` but found `<unknown>`"

    // post 2/6/2025:
    // due to the changes in `parser`,
    // this is now parsed as:
    // ```text
    //  x : i32 = .[]
    // ```
    // which honestly makes more sense
    //
    // I added `int_literal_as_type` and `unknown_as_type` to try and check for the same thing
    // this test was originally checking for
    check(
        r#"
            foo :: () {
                x : i32.[];
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : ~[0]void
            2 : void
            3 : () -> void
            l0 : i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                    found: Ty::AnonArray {
                        size: 0,
                        sub_ty: Ty::Void.into(),
                    }
                    .into(),
                },
                48..51,
                None,
            )]
        },
    )
}

#[test]
fn int_literal_as_type() {
    check(
        r#"
            foo :: () {
                x : 42;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : void
            2 : () -> void
            l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Type.into()),
                    found: Ty::UInt(0).into(),
                },
                45..47,
                None,
            )]
        },
    )
}

#[test]
fn unknown_as_type() {
    // this is just to make sure that the compiler doens't show a diagnostic
    // like "expected `type` but found `<unknown>`"
    check(
        r#"
            foo :: () {
                x : _;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : void
            2 : () -> void
            l0 : <unknown>
        "#]],
        |_| [],
    )
}

#[test]
fn type_names() {
    check(
        r#"
            My_Struct :: struct { a: i32 };
            My_Distinct :: distinct ();
            My_Enum :: enum { Foo, Bar };
            My_Int :: i32;

            foo :: (a: My_Struct, b: My_Distinct, c: My_Enum, d: My_Int) {}
        "#,
        expect![[r#"
            main::My_Distinct : type
            main::My_Enum : type
            main::My_Int : type
            main::My_Struct : type
            main::foo : (main::My_Struct, main::My_Distinct, main::My_Enum, i32) -> void
            1 : type
            2 : void
            3 : type
            4 : type
            5 : type
            10 : void
            11 : (main::My_Struct, main::My_Distinct, main::My_Enum, i32) -> void
        "#]],
        |i| {
            println!("{:?}", get_all_named_types());
            let struct_name = get_type_name(
                Ty::ConcreteStruct {
                    uid: 0,
                    members: vec![MemberTy {
                        name: hir::Name(i.intern("a")),
                        ty: Ty::IInt(32).into(),
                    }],
                }
                .into(),
            );
            assert_eq!(
                struct_name,
                Some(TyName::Global(hir::Fqn {
                    file: hir::FileName(i.intern("main.capy")),
                    name: hir::Name(i.intern("My_Struct"))
                }))
            );

            let distinct_name = get_type_name(
                Ty::Distinct {
                    uid: 1,
                    sub_ty: Ty::Void.into(),
                }
                .into(),
            );
            assert_eq!(
                distinct_name,
                Some(TyName::Global(hir::Fqn {
                    file: hir::FileName(i.intern("main.capy")),
                    name: hir::Name(i.intern("My_Distinct"))
                }))
            );

            let enum_name = get_type_name(
                Ty::Enum {
                    uid: 4,
                    variants: vec![
                        Ty::EnumVariant {
                            enum_uid: 4,
                            variant_name: hir::Name(i.intern("Foo")),
                            uid: 2,
                            sub_ty: Ty::Void.into(),
                            discriminant: 0,
                        }
                        .into(),
                        Ty::EnumVariant {
                            enum_uid: 4,
                            variant_name: hir::Name(i.intern("Bar")),
                            uid: 3,
                            sub_ty: Ty::Void.into(),
                            discriminant: 1,
                        }
                        .into(),
                    ],
                }
                .into(),
            );
            assert_eq!(
                enum_name,
                Some(TyName::Global(hir::Fqn {
                    file: hir::FileName(i.intern("main.capy")),
                    name: hir::Name(i.intern("My_Enum"))
                }))
            );

            let int_name = get_type_name(Ty::IInt(32).into());
            assert_eq!(int_name, None);

            []
        },
    )
}

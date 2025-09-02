use super::*;

use expect_test::expect;

#[test]
fn struct_literal() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            foo :: () {
                some_guy := Person.{
                    name = "Joe Schmoe",
                    age = 31,
                };
            };
        "#,
        expect![[r#"
            main::Person : type
            main::foo : () -> void
            2 : type
            4 : str
            5 : i32
            6 : main::Person
            7 : void
            8 : () -> void
            l0 : main::Person
        "#]],
        |_| [],
    );
}

#[test]
fn struct_literal_wrong_fields() {
    // todo: these are the kind of errors that should be reported for assigning an anonymous struct to a known struct
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            foo :: () {
                some_guy := Person.{
                    name = false,
                    height = "5'9\""
                };
            };
        "#,
        expect![[r#"
            main::Person : type
            main::foo : () -> void
            2 : type
            4 : bool
            5 : str
            6 : main::Person
            7 : void
            8 : () -> void
            l0 : main::Person
        "#]],
        |i| {
            let person_ty = Ty::ConcreteStruct {
                uid: 0,
                members: vec![
                    MemberTy {
                        name: hir::Name(i.intern("name")),
                        ty: Ty::String.into(),
                    },
                    MemberTy {
                        name: hir::Name(i.intern("age")),
                        ty: Ty::IInt(32).into(),
                    },
                ],
            }
            .into();

            [
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::String.into()),
                        found: Ty::Bool.into(),
                    },
                    188..193,
                    None,
                ),
                (
                    TyDiagnosticKind::NonExistentMember {
                        member: i.intern("height"),
                        found_ty: person_ty,
                    },
                    215..221,
                    None,
                ),
                (
                    TyDiagnosticKind::StructLiteralMissingMember {
                        member: i.intern("age"),
                        expected_ty: person_ty,
                    },
                    152..249,
                    None,
                ),
            ]
        },
    );
}

#[test]
fn get_struct_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            foo :: () -> i32 {
                some_guy := Person.{
                    name = "Joe Schmoe",
                    age = 31,
                };

                some_guy.age
            };
        "#,
        expect![[r#"
            main::Person : type
            main::foo : () -> i32
            2 : type
            5 : str
            6 : i32
            7 : main::Person
            8 : main::Person
            9 : i32
            10 : i32
            11 : () -> i32
            l0 : main::Person
        "#]],
        |_| [],
    );
}

#[test]
fn non_existent_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            foo :: () -> i32 {
                some_guy := Person.{
                    name = "Joe Schmoe",
                    age = 31,
                };

                some_guy.height
            };
        "#,
        expect![[r#"
            main::Person : type
            main::foo : () -> i32
            2 : type
            5 : str
            6 : i32
            7 : main::Person
            8 : main::Person
            9 : <unknown>
            10 : <unknown>
            11 : () -> i32
            l0 : main::Person
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NonExistentMember {
                    member: i.intern("height"),
                    found_ty: Ty::ConcreteStruct {
                        uid: 0,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("name")),
                                ty: Ty::String.into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("age")),
                                ty: Ty::IInt(32).into(),
                            },
                        ],
                    }
                    .into(),
                },
                275..290,
                None,
            )]
        },
    );
}

#[test]
fn no_implicit_struct_cast() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: i8,
            };

            Bar :: struct {
                a: i32,
                b: i8,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = 2,
                };

                my_bar : Bar = my_foo;
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            2 : type
            5 : type
            8 : i32
            9 : i8
            10 : main::Foo
            12 : main::Foo
            13 : void
            14 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteStruct {
                            uid: 1,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::IInt(8).into(),
                                },
                            ],
                        }
                        .into(),
                    ),
                    found: Ty::ConcreteStruct {
                        uid: 0,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::IInt(8).into(),
                            },
                        ],
                    }
                    .into(),
                },
                350..356,
                None,
            )]
        },
    );
}

#[test]
fn cast_struct_same_fields() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: i8,
            };

            Bar :: struct {
                a: i32,
                b: i8,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = 2,
                };

                my_bar : Bar = Bar.(my_foo);
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            2 : type
            5 : type
            8 : i32
            9 : i8
            10 : main::Foo
            12 : main::Foo
            14 : main::Bar
            15 : void
            16 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |_| [],
    );
}

#[test]
fn cast_struct_diff_field_order() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: i8,
            };

            Bar :: struct {
                b: i8,
                a: i32,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = 2,
                };

                my_bar : Bar = Bar.(my_foo);
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            2 : type
            5 : type
            8 : i32
            9 : i8
            10 : main::Foo
            12 : main::Foo
            14 : main::Bar
            15 : void
            16 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |_| [],
    );
}

#[test]
fn cast_struct_diff_field_ty_castable() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: i8,
            };

            Bar :: struct {
                a: i32,
                b: i16,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = 2,
                };

                my_bar : Bar = Bar.(my_foo);
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            2 : type
            5 : type
            8 : i32
            9 : i8
            10 : main::Foo
            12 : main::Foo
            14 : main::Bar
            15 : void
            16 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |_| [],
    );
}

#[test]
fn cast_struct_diff_field_ty_uncastable() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: [2]i32,
            };

            Bar :: struct {
                a: i32,
                b: [3]i32,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = .[2, 3],
                };

                my_bar : Bar = Bar.(my_foo);
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            1 : usize
            4 : type
            6 : usize
            9 : type
            12 : i32
            13 : i32
            14 : i32
            15 : [2]i32
            16 : main::Foo
            18 : main::Foo
            20 : main::Bar
            21 : void
            22 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Uncastable {
                    from: Ty::ConcreteStruct {
                        uid: 0,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::ConcreteArray {
                                    size: 2,
                                    sub_ty: Ty::IInt(32).into(),
                                }
                                .into(),
                            },
                        ],
                    }
                    .into(),
                    to: Ty::ConcreteStruct {
                        uid: 1,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::ConcreteArray {
                                    size: 3,
                                    sub_ty: Ty::IInt(32).into(),
                                }
                                .into(),
                            },
                        ],
                    }
                    .into(),
                },
                364..376,
                None,
            )]
        },
    );
}

#[test]
fn cast_struct_diff_field_name() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: i8,
            };

            Bar :: struct {
                x: i32,
                y: i8,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = 2,
                };

                my_bar : Bar = Bar.(my_foo);
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            2 : type
            5 : type
            8 : i32
            9 : i8
            10 : main::Foo
            12 : main::Foo
            14 : main::Bar
            15 : void
            16 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Uncastable {
                    from: Ty::ConcreteStruct {
                        uid: 0,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::IInt(8).into(),
                            },
                        ],
                    }
                    .into(),
                    to: Ty::ConcreteStruct {
                        uid: 1,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("x")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("y")),
                                ty: Ty::IInt(8).into(),
                            },
                        ],
                    }
                    .into(),
                },
                350..362,
                None,
            )]
        },
    );
}

#[test]
fn cast_struct_diff_field_len() {
    check(
        r#"
            Foo :: struct {
                a: i32,
                b: i8,
            };

            Bar :: struct {
                a: i32,
                b: i8,
                c: str,
            };

            main :: () {
                my_foo : Foo = Foo.{
                    a = 1,
                    b = 2,
                };

                my_bar : Bar = Bar.(my_foo);
            };
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::main : () -> void
            2 : type
            6 : type
            9 : i32
            10 : i8
            11 : main::Foo
            13 : main::Foo
            15 : main::Bar
            16 : void
            17 : () -> void
            l0 : main::Foo
            l1 : main::Bar
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Uncastable {
                    from: Ty::ConcreteStruct {
                        uid: 0,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::IInt(8).into(),
                            },
                        ],
                    }
                    .into(),
                    to: Ty::ConcreteStruct {
                        uid: 1,
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::IInt(32).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::IInt(8).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("c")),
                                ty: Ty::String.into(),
                            },
                        ],
                    }
                    .into(),
                },
                374..386,
                None,
            )]
        },
    );
}

#[test]
fn field_of_struct_ptr() {
    check(
        r#"
            Foo :: struct {
                a: i32
            };

            main :: () {
                my_foo := Foo.{
                    a = 25
                };

                ptr := ^my_foo;

                ptr.a;
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            1 : type
            3 : i32
            4 : main::Foo
            5 : main::Foo
            6 : ^main::Foo
            7 : ^main::Foo
            8 : i32
            9 : void
            10 : () -> void
            l0 : main::Foo
            l1 : ^main::Foo
        "#]],
        |_| [],
    );
}

#[test]
fn field_of_struct_ptr_ptr() {
    check(
        r#"
            Foo :: struct {
                a: i32
            };

            main :: () {
                my_foo := Foo.{
                    a = 25
                };

                ptr := ^^my_foo;

                ptr.a;
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            1 : type
            3 : i32
            4 : main::Foo
            5 : main::Foo
            6 : ^main::Foo
            7 : ^^main::Foo
            8 : ^^main::Foo
            9 : i32
            10 : void
            11 : () -> void
            l0 : main::Foo
            l1 : ^^main::Foo
        "#]],
        |_| [],
    );
}

#[test]
fn field_of_non_struct_ptr_ptr() {
    check(
        r#"
            main :: () {
                my_foo := 5;

                ptr := ^^my_foo;

                ptr.a;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^{uint}
            3 : ^^{uint}
            4 : ^^{uint}
            5 : <unknown>
            6 : void
            7 : () -> void
            l0 : {uint}
            l1 : ^^{uint}
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NonExistentMember {
                    member: i.intern("a"),
                    found_ty: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                106..111,
                None,
            )]
        },
    );
}

#[test]
fn non_existent_field_of_struct_ptr_ptr() {
    check(
        r#"
            Foo :: struct {
                a: i32
            };

            main :: () {
                my_foo := Foo.{
                    a = 25
                };

                ptr := ^^my_foo;

                ptr.b;
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            1 : type
            3 : i32
            4 : main::Foo
            5 : main::Foo
            6 : ^main::Foo
            7 : ^^main::Foo
            8 : ^^main::Foo
            9 : <unknown>
            10 : void
            11 : () -> void
            l0 : main::Foo
            l1 : ^^main::Foo
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NonExistentMember {
                    member: i.intern("b"),
                    found_ty: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::ConcreteStruct {
                                uid: 0,
                                members: vec![MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                }],
                            }
                            .into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                222..227,
                None,
            )]
        },
    );
}

#[test]
fn mutate_field_of_struct_ptr_ptr() {
    check(
        r#"
            Foo :: struct {
                a: i32
            };

            main :: () {
                my_foo := Foo.{
                    a = 25
                };

                ptr := ^mut ^mut my_foo;

                ptr.a = 5;
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            1 : type
            3 : i32
            4 : main::Foo
            5 : main::Foo
            6 : ^mut main::Foo
            7 : ^mut ^mut main::Foo
            8 : ^mut ^mut main::Foo
            9 : i32
            10 : i32
            11 : void
            12 : () -> void
            l0 : main::Foo
            l1 : ^mut ^mut main::Foo
        "#]],
        |_| [],
    );
}

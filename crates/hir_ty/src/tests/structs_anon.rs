use super::*;

use expect_test::expect;

#[test]
fn anon_struct() {
    check(
        r#"
            anon :: () {
                foo := .{
                    a = 5,
                    b = "hello",
                    c = 5.5,
                };
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : str
            2 : {float}
            3 : ~struct {a: {uint}, b: str, c: {float}}
            4 : void
            5 : () -> void
            l0 : ~struct {a: {uint}, b: str, c: {float}}
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_into_known_struct() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo : Foo_Type = .{
                    a = 5,
                    b = "hello",
                    c = 5.5,
                };
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            5 : u8
            6 : str
            7 : f64
            8 : main::Foo_Type
            9 : void
            10 : () -> void
            l0 : main::Foo_Type
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_into_known_struct_mixed_fields() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo : Foo_Type = .{
                    b = "hello",
                    c = 5.5,
                    a = 5,
                };
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            5 : str
            6 : f64
            7 : u8
            8 : main::Foo_Type
            9 : void
            10 : () -> void
            l0 : main::Foo_Type
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_into_known_struct_by_inference() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo := .{
                    b = "hello",
                    c = 5.5,
                    a = 5,
                };

                bar : Foo_Type = foo;
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            4 : str
            5 : f64
            6 : u8
            7 : main::Foo_Type
            9 : main::Foo_Type
            10 : void
            11 : () -> void
            l0 : main::Foo_Type
            l1 : main::Foo_Type
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_as_known_struct() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo := .{
                    b = "hello",
                    c = 5.5,
                    a = 5,
                };

                bar := Foo_Type.(foo);
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            4 : str
            5 : f64
            6 : u8
            7 : main::Foo_Type
            8 : main::Foo_Type
            10 : main::Foo_Type
            11 : void
            12 : () -> void
            l0 : main::Foo_Type
            l1 : main::Foo_Type
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_as_known_struct_diff_field_ty() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                c : f32 = 5.5;

                foo := Foo_Type.(.{
                    b = "hello",
                    c = c,
                    a = 3.14,
                });
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            5 : f32
            6 : str
            7 : f32
            8 : {float}
            9 : ~struct {b: str, c: f32, a: {float}}
            11 : main::Foo_Type
            12 : void
            13 : () -> void
            l0 : f32
            l1 : main::Foo_Type
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_into_known_struct_missing_field() {
    // todo: the diag should look better than just
    // "expected `Foo_Type` but found `struct {a: {uint}, b: str}`"
    // maybe there should be a help visual to see which fields don't match
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo : Foo_Type = .{
                    a = 5,
                    b = "hello",
                };
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            5 : {uint}
            6 : str
            7 : ~struct {a: {uint}, b: str}
            8 : void
            9 : () -> void
            l0 : main::Foo_Type
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteStruct {
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::UInt(8).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("c")),
                                    ty: Ty::Float(64).into(),
                                },
                            ],
                        }
                        .into(),
                    ),
                    found: Ty::AnonStruct {
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::UInt(0).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::String.into(),
                            },
                        ],
                    }
                    .into(),
                },
                179..259,
                None,
            )]
        },
    )
}

#[test]
fn anon_struct_into_known_struct_extra_field() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo : Foo_Type = .{
                    a = 5,
                    b = "hello",
                    c = 3.14,
                    d = true,
                };
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            5 : {uint}
            6 : str
            7 : {float}
            8 : bool
            9 : ~struct {a: {uint}, b: str, c: {float}, d: bool}
            10 : void
            11 : () -> void
            l0 : main::Foo_Type
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteStruct {
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::UInt(8).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("c")),
                                    ty: Ty::Float(64).into(),
                                },
                            ],
                        }
                        .into(),
                    ),
                    found: Ty::AnonStruct {
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::UInt(0).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::String.into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("c")),
                                ty: Ty::Float(0).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("d")),
                                ty: Ty::Bool.into(),
                            },
                        ],
                    }
                    .into(),
                },
                179..319,
                None,
            )]
        },
    )
}

#[test]
fn anon_struct_into_known_struct_misnamed_field() {
    check(
        r#"
            Foo_Type :: struct {
                a: u8,
                b: str,
                c: f64,
            };

            anon :: () {
                foo : Foo_Type = .{
                    a = 5,
                    b = "hello",
                    last = 0.3,
                };
            }
        "#,
        expect![[r#"
            main::Foo_Type : type
            main::anon : () -> void
            3 : type
            5 : {uint}
            6 : str
            7 : {float}
            8 : ~struct {a: {uint}, b: str, last: {float}}
            9 : void
            10 : () -> void
            l0 : main::Foo_Type
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteStruct {
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::UInt(8).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("c")),
                                    ty: Ty::Float(64).into(),
                                },
                            ],
                        }
                        .into(),
                    ),
                    found: Ty::AnonStruct {
                        members: vec![
                            MemberTy {
                                name: hir::Name(i.intern("a")),
                                ty: Ty::UInt(0).into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("b")),
                                ty: Ty::String.into(),
                            },
                            MemberTy {
                                name: hir::Name(i.intern("last")),
                                ty: Ty::Float(0).into(),
                            },
                        ],
                    }
                    .into(),
                },
                179..291,
                None,
            )]
        },
    )
}

#[test]
fn anon_struct_field() {
    check(
        r#"
            anon :: () {
                foo := .{
                    a = 5,
                    b = "hello",
                    c = 5.5,
                };

                foo.a;
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : str
            2 : {float}
            3 : ~struct {a: {uint}, b: str, c: {float}}
            4 : ~struct {a: {uint}, b: str, c: {float}}
            5 : {uint}
            6 : void
            7 : () -> void
            l0 : ~struct {a: {uint}, b: str, c: {float}}
        "#]],
        |_| [],
    )
}

#[test]
fn anon_struct_field_mutation() {
    // todo: check if `10` will get a type of `i32` if later the struct becomes concrete
    check(
        r#"
            anon :: () {
                foo := .{
                    a = 5,
                    b = "hello",
                    c = 5.5,
                };

                foo.a = 10;
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : str
            2 : {float}
            3 : ~struct {a: {uint}, b: str, c: {float}}
            4 : ~struct {a: {uint}, b: str, c: {float}}
            5 : {uint}
            6 : {uint}
            7 : void
            8 : () -> void
            l0 : ~struct {a: {uint}, b: str, c: {float}}
        "#]],
        |_| [],
    )
}

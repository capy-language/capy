use super::*;

use expect_test::expect;

#[test]
fn default_value_i32() {
    check(
        r#"
            defaults :: () {
                x : i32;
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            1 : void
            2 : () -> void
            l0 : i32
        "#]],
        |_| [],
    )
}

#[test]
fn default_value_char_array() {
    check(
        r#"
            defaults :: () {
                x : [10]char;
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            0 : usize
            3 : void
            4 : () -> void
            l0 : [10]char
        "#]],
        |_| [],
    )
}

#[test]
fn default_value_distinct_distinct_struct_with_valid_types() {
    check(
        r#"
            defaults :: () {
                x : distinct distinct struct {
                    a: [2][4]u8,
                    b: i16,
                    c: distinct f32,
                    d: bool,
                    e: char,
                    f: void,
                };
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            0 : usize
            1 : usize
            14 : void
            15 : () -> void
            l0 : distinct'3 distinct'2 struct'1 {a: [2][4]u8, b: i16, c: distinct'0 f32, d: bool, e: char, f: void}
        "#]],
        |_| [],
    )
}

#[test]
fn default_value_i32_ptr() {
    check(
        r#"
            defaults :: () {
                x : ^i32;
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            2 : void
            3 : () -> void
            l0 : ^i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::DeclTypeHasNoDefault {
                    ty: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                },
                50..54,
                None,
            )]
        },
    )
}

#[test]
fn default_value_opt_i32_ptr() {
    check(
        r#"
            defaults :: () {
                x : ?^i32;
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            3 : void
            4 : () -> void
            l0 : ?^i32
        "#]],
        |_| [],
    )
}

#[test]
fn default_value_distinct_bool_slice() {
    check(
        r#"
            defaults :: () {
                x : distinct []bool;
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            3 : void
            4 : () -> void
            l0 : distinct'0 []bool
        "#]],
        |_| {
            [(
                TyDiagnosticKind::DeclTypeHasNoDefault {
                    ty: Ty::Distinct {
                        uid: 0,
                        sub_ty: Ty::Slice {
                            sub_ty: Ty::Bool.into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                50..65,
                None,
            )]
        },
    )
}

#[test]
fn default_value_distinct_struct_with_str() {
    check(
        r#"
            defaults :: () {
                x : distinct struct {
                    foo: str,
                    bar: u8,
                };
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            4 : void
            5 : () -> void
            l0 : distinct'1 struct'0 {foo: str, bar: u8}
        "#]],
        |i| {
            [(
                TyDiagnosticKind::DeclTypeHasNoDefault {
                    ty: Ty::Distinct {
                        uid: 1,
                        sub_ty: Ty::ConcreteStruct {
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("foo")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("bar")),
                                    ty: Ty::UInt(8).into(),
                                },
                            ],
                        }
                        .into(),
                    }
                    .into(),
                },
                50..144,
                None,
            )]
        },
    )
}

#[test]
fn default_value_distinct_struct_with_opt_str() {
    check(
        r#"
            defaults :: () {
                x : distinct struct {
                    foo: ?str,
                    bar: u8,
                };
            }
        "#,
        expect![[r#"
            main::defaults : () -> void
            5 : void
            6 : () -> void
            l0 : distinct'1 struct'0 {foo: ?str, bar: u8}
        "#]],
        |_| [],
    )
}

#[test]
fn default_value_with_uninferred_globals() {
    // this is to check for a bug where errors would get reported twice
    // because when an uninferred global was reached it would
    // throw away all the previously done statement inferring.
    check(
        r#"
            Foo :: distinct u8;
            Bar :: ^Foo;
            Baz :: struct { a: Bar };

            defaults :: () {
                x: ^i32;
                Baz;
            }
        "#,
        expect![[r#"
            main::Bar : type
            main::Baz : type
            main::Foo : type
            main::defaults : () -> void
            1 : type
            2 : type
            3 : type
            5 : type
            8 : type
            9 : void
            10 : () -> void
            l0 : ^i32
        "#]],
        |_| {
            // under the bug, this appears twice
            [(
                TyDiagnosticKind::DeclTypeHasNoDefault {
                    ty: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                },
                145..149,
                None,
            )]
        },
    )
}

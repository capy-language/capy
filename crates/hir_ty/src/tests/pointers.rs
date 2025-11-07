use super::*;

use expect_test::expect;

#[test]
fn ref_infer() {
    check(
        r#"
            main :: () -> ^i32 {
                x := 42;

                ^x
            };
        "#,
        expect![[r#"
            main::main : main::main() -> ^i32
              6 : main::main() -> ^i32
            main::lambda#main : main::main() -> ^i32
              2 : i32
              3 : i32
              4 : ^i32
              5 : ^i32
              6 : main::main() -> ^i32
              l0 : i32
        "#]],
        |_| [],
    );
}

#[test]
fn mut_ref_to_binding() {
    check(
        r#"
            main :: () {
                foo :: 5;
                bar :: ^mut foo;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              4 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : {uint}
              1 : {uint}
              2 : ^mut {uint}
              3 : void
              4 : main::main() -> void
              l0 : {uint}
              l1 : ^mut {uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MutableRefToImmutableData,
                75..83,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 42..51)),
            )]
        },
    );
}

#[test]
fn ref_to_param_ref() {
    check(
        r#"
            foo :: (x: ^i32) {
                ^x;
            }
        "#,
        expect![[r#"
            main::foo : main::foo(^i32) -> void
              5 : main::foo(^i32) -> void
            main::lambda#foo : main::foo(^i32) -> void
              2 : ^i32
              3 : ^^i32
              4 : void
              5 : main::foo(^i32) -> void
        "#]],
        |_| [],
    );
}

#[test]
fn mut_ref_to_param_ref() {
    check(
        r#"
            foo :: (x: ^i32) {
                ^mut x;
            }
        "#,
        expect![[r#"
            main::foo : main::foo(^i32) -> void
              5 : main::foo(^i32) -> void
            main::lambda#foo : main::foo(^i32) -> void
              2 : ^i32
              3 : ^mut ^i32
              4 : void
              5 : main::foo(^i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MutableRefToImmutableData,
                48..54,
                Some((
                    TyDiagnosticHelpKind::ImmutableParam { assignment: false },
                    21..28,
                )),
            )]
        },
    );
}

#[test]
fn mut_ref_to_param_mut_ref() {
    check(
        r#"
            foo :: (x: ^mut i32) {
                ^mut x;
            }
        "#,
        expect![[r#"
            main::foo : main::foo(^mut i32) -> void
              5 : main::foo(^mut i32) -> void
            main::lambda#foo : main::foo(^mut i32) -> void
              2 : ^mut i32
              3 : ^mut ^mut i32
              4 : void
              5 : main::foo(^mut i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MutableRefToImmutableData,
                52..58,
                Some((
                    TyDiagnosticHelpKind::ImmutableParam { assignment: false },
                    21..32,
                )),
            )]
        },
    );
}

#[test]
fn mut_ref_to_immutable_ref() {
    check(
        r#"
            foo :: () {
                bar := 5;

                baz :: ^bar;

                ^mut baz;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : ^{uint}
              3 : ^{uint}
              4 : ^mut ^{uint}
              5 : void
              6 : main::foo() -> void
              l0 : {uint}
              l1 : ^{uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MutableRefToImmutableData,
                98..106,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 68..80)),
            )]
        },
    );
}

#[test]
fn mut_ref_to_mut_ref_binding() {
    check(
        r#"
            foo :: () {
                bar := 5;

                baz :: ^mut bar;

                ^mut baz;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : ^mut {uint}
              3 : ^mut {uint}
              4 : ^mut ^mut {uint}
              5 : void
              6 : main::foo() -> void
              l0 : {uint}
              l1 : ^mut {uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MutableRefToImmutableData,
                102..110,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 68..84)),
            )]
        },
    );
}

#[test]
fn pass_mut_ref_to_immutable_ref() {
    check(
        r#"
            main :: () {
                foo := 5;

                bar(^mut foo);
            };

            bar :: (x: ^i32) {};
        "#,
        expect![[r#"
            main::main : main::main() -> void
              6 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : i32
              1 : main::bar(^i32) -> void
              2 : i32
              3 : ^mut i32
              4 : void
              5 : void
              6 : main::main() -> void
              l0 : i32
            main::bar : main::bar(^i32) -> void
              10 : main::bar(^i32) -> void
            main::lambda#bar : main::bar(^i32) -> void
              9 : void
              10 : main::bar(^i32) -> void
        "#]],
        |_| [],
    );
}

#[test]
fn pass_immutable_ref_to_mut_ref() {
    check(
        r#"
            main :: () {
                foo := 5;

                bar(^foo);
            };

            bar :: (x: ^mut i32) {};
        "#,
        expect![[r#"
            main::main : main::main() -> void
              6 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : {uint}
              1 : main::bar(^mut i32) -> void
              2 : {uint}
              3 : ^{uint}
              4 : void
              5 : void
              6 : main::main() -> void
              l0 : {uint}
            main::bar : main::bar(^mut i32) -> void
              10 : main::bar(^mut i32) -> void
            main::lambda#bar : main::bar(^mut i32) -> void
              9 : void
              10 : main::bar(^mut i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Pointer {
                            mutable: true,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    ),
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::UInt(0).into(),
                    }
                    .into(),
                },
                73..77,
                None,
            )]
        },
    );
}

#[test]
fn deref_non_pointer() {
    check(
        r#"
            foo :: () {
                wow := "Wow!";

                wow^;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              4 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              1 : str
              2 : <unknown>
              3 : void
              4 : main::foo() -> void
              l0 : str
        "#]],
        |_| {
            [(
                TyDiagnosticKind::DerefNonPointer {
                    found: Ty::String.into(),
                },
                73..77,
                None,
            )]
        },
    );
}

#[test]
fn weak_int_ptr_to_strong_int_ptr() {
    check(
        r#"
            main :: () {
                x := 42;
                x := ^x;

                y : ^i32 = x;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              7 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : i32
              1 : i32
              2 : ^i32
              5 : ^i32
              6 : void
              7 : main::main() -> void
              l0 : i32
              l1 : ^i32
              l2 : ^i32
        "#]],
        |_| [],
    );
}

#[test]
fn weak_float_ptr_to_strong_int_ptr() {
    check(
        r#"
            main :: () {
                x := 3.2;
                x := ^x;

                y : ^i32 = x;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              7 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : {float}
              1 : {float}
              2 : ^{float}
              5 : ^{float}
              6 : void
              7 : main::main() -> void
              l0 : {float}
              l1 : ^{float}
              l2 : ^i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    ),
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Float(0).into(),
                    }
                    .into(),
                },
                105..106,
                None,
            )]
        },
    );
}

#[test]
fn weak_struct_ptr_to_strong_struct_ptr() {
    check(
        r#"
            My_Struct :: struct {
                a: i32,
            };

            main :: () {
                x := .{
                    a = 42,
                };
                x := ^x;

                y : ^My_Struct = x;
            };
        "#,
        expect![[r#"
            main::My_Struct : type
              1 : type
            main::main : main::main() -> void
              10 : main::main() -> void
            main::lambda#main : main::main() -> void
              2 : {uint}
              3 : ~struct {a: {uint}}
              4 : ~struct {a: {uint}}
              5 : ^~struct {a: {uint}}
              8 : ^~struct {a: {uint}}
              9 : void
              10 : main::main() -> void
              l0 : ~struct {a: {uint}}
              l1 : ^~struct {a: {uint}}
              l2 : ^main::My_Struct
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::ConcreteStruct {
                                uid: 0,
                                members: vec![MemberTy {
                                    name: Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                }],
                            }
                            .into(),
                        }
                        .into(),
                    ),
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::AnonStruct {
                            members: vec![MemberTy {
                                name: Name(i.intern("a")),
                                ty: Ty::UInt(0).into(),
                            }],
                        }
                        .into(),
                    }
                    .into(),
                },
                230..231,
                None,
            )]
        },
    );
}

#[test]
fn small_strong_ptr_to_big_strong_ptr() {
    check(
        r#"
            main :: () {
                x : i8 = 42;
                x := ^x;

                y : ^i32 = x;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              8 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : i8
              2 : i8
              3 : ^i8
              6 : ^i8
              7 : void
              8 : main::main() -> void
              l0 : i8
              l1 : ^i8
              l2 : ^i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    ),
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::IInt(8).into(),
                    }
                    .into(),
                },
                108..109,
                None,
            )]
        },
    );
}

#[test]
fn same_strong_ptr_to_strong_ptr() {
    check(
        r#"
            main :: () {
                x : i32 = 42;
                x := ^x;

                y : ^i32 = x;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              8 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : i32
              2 : i32
              3 : ^i32
              6 : ^i32
              7 : void
              8 : main::main() -> void
              l0 : i32
              l1 : ^i32
              l2 : ^i32
        "#]],
        |_| [],
    );
}

#[test]
fn distinct_ptr_to_non_distinct_ptr() {
    check(
        r#"
            My_Type :: distinct i32;

            main :: () {
                x : My_Type = 42;
                x := ^x;

                y : ^i32 = x;
            };
        "#,
        expect![[r#"
            main::My_Type : type
              1 : type
            main::main : main::main() -> void
              10 : main::main() -> void
            main::lambda#main : main::main() -> void
              3 : main::My_Type
              4 : main::My_Type
              5 : ^main::My_Type
              8 : ^main::My_Type
              9 : void
              10 : main::main() -> void
              l0 : main::My_Type
              l1 : ^main::My_Type
              l2 : ^i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    ),
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Distinct {
                            uid: 0,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                151..152,
                None,
            )]
        },
    );
}

#[test]
fn non_distinct_ptr_to_distinct_ptr() {
    check(
        r#"
            My_Type :: distinct i32;

            main :: () {
                x : i32 = 42;
                x := ^x;

                y : ^My_Type = x;
            };
        "#,
        expect![[r#"
            main::My_Type : type
              1 : type
            main::main : main::main() -> void
              10 : main::main() -> void
            main::lambda#main : main::main() -> void
              3 : i32
              4 : i32
              5 : ^i32
              8 : ^i32
              9 : void
              10 : main::main() -> void
              l0 : i32
              l1 : ^i32
              l2 : ^main::My_Type
        "#]],
        |_| [],
    );
}

use super::*;

use expect_test::expect;

#[test]
fn is_variant_directive() {
    check(
        r#"
            Web_Event :: enum {
                Page_Load,
                Page_Unload,
                Key_Press: char,
                Paste: str,
                Click: struct {
                    x: i64,
                    y: i64,
                },
            };

            foo :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                is := #is_variant(clicked, Web_Event.Click);
            }
        "#,
        expect![[r#"
            main::Web_Event : type
              5 : type
            main::foo : main::foo() -> void
              17 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : type
              9 : i64
              10 : i64
              11 : main::Web_Event.Click
              12 : main::Web_Event
              13 : type
              14 : type
              15 : bool
              16 : void
              17 : main::foo() -> void
              l0 : main::Web_Event
              l1 : bool
        "#]],
        |_| [],
    )
}

#[test]
fn is_variant_directive_no_args() {
    check(
        r#"
            foo :: () {
                is := #is_variant();
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              2 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : <unknown>
              1 : void
              2 : main::foo() -> void
              l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MissingArg {
                    expected: ExpectedTy::SumType,
                },
                59..59,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_non_sum_type() {
    check(
        r#"
            foo :: () {
                is := #is_variant(5);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              3 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : <unknown>
              2 : void
              3 : main::foo() -> void
              l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::SumType,
                    found: Ty::UInt(0).into(),
                },
                59..60,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_enum_with_non_type() {
    check(
        r#"
            Web_Event :: enum {
                Page_Load,
                Page_Unload,
                Key_Press: char,
                Paste: str,
                Click: struct {
                    x: i64,
                    y: i64,
                },
            };

            foo :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                is := #is_variant(clicked, 5);
            }
        "#,
        expect![[r#"
            main::Web_Event : type
              5 : type
            main::foo : main::foo() -> void
              16 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : type
              9 : i64
              10 : i64
              11 : main::Web_Event.Click
              12 : main::Web_Event
              13 : {uint}
              14 : <unknown>
              15 : void
              16 : main::foo() -> void
              l0 : main::Web_Event
              l1 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Type.into()),
                    found: Ty::UInt(0).into(),
                },
                471..472,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_enum_with_type_incorrect() {
    check(
        r#"
            Web_Event :: enum {
                Page_Load,
                Page_Unload,
                Key_Press: char,
                Paste: str,
                Click: struct {
                    x: i64,
                    y: i64,
                },
            };

            foo :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                is := #is_variant(clicked, i32);
            }
        "#,
        expect![[r#"
            main::Web_Event : type
              5 : type
            main::foo : main::foo() -> void
              16 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : type
              9 : i64
              10 : i64
              11 : main::Web_Event.Click
              12 : main::Web_Event
              13 : type
              14 : <unknown>
              15 : void
              16 : main::foo() -> void
              l0 : main::Web_Event
              l1 : <unknown>
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotAVariantOfSumType {
                    ty: Ty::IInt(32).into(),
                    sum_ty: Ty::Enum {
                        uid: 6,
                        variants: vec![
                            Ty::EnumVariant {
                                enum_uid: 6,
                                variant_name: Name(i.intern("Page_Load")),
                                uid: 0,
                                sub_ty: Ty::Void.into(),
                                discriminant: 0,
                            }
                            .into(),
                            Ty::EnumVariant {
                                enum_uid: 6,
                                variant_name: Name(i.intern("Page_Unload")),
                                uid: 1,
                                sub_ty: Ty::Void.into(),
                                discriminant: 1,
                            }
                            .into(),
                            Ty::EnumVariant {
                                enum_uid: 6,
                                variant_name: Name(i.intern("Key_Press")),
                                uid: 2,
                                sub_ty: Ty::Char.into(),
                                discriminant: 2,
                            }
                            .into(),
                            Ty::EnumVariant {
                                enum_uid: 6,
                                variant_name: Name(i.intern("Paste")),
                                uid: 3,
                                sub_ty: Ty::String.into(),
                                discriminant: 3,
                            }
                            .into(),
                            Ty::EnumVariant {
                                enum_uid: 6,
                                variant_name: Name(i.intern("Click")),
                                uid: 5,
                                sub_ty: Ty::ConcreteStruct {
                                    uid: 4,
                                    members: vec![
                                        MemberTy {
                                            name: Name(i.intern("x")),
                                            ty: Ty::IInt(64).into(),
                                        },
                                        MemberTy {
                                            name: Name(i.intern("y")),
                                            ty: Ty::IInt(64).into(),
                                        },
                                    ],
                                }
                                .into(),
                                discriminant: 4,
                            }
                            .into(),
                        ],
                    }
                    .into(),
                },
                471..474,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_enum_extra_arg() {
    check(
        r#"
            Web_Event :: enum {
                Page_Load,
                Page_Unload,
                Key_Press: char,
                Paste: str,
                Click: struct {
                    x: i64,
                    y: i64,
                },
            };

            foo :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                is := #is_variant(clicked, Web_Event.Click, 42, bool);
            }
        "#,
        expect![[r#"
            main::Web_Event : type
              5 : type
            main::foo : main::foo() -> void
              19 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : type
              9 : i64
              10 : i64
              11 : main::Web_Event.Click
              12 : main::Web_Event
              13 : type
              14 : type
              15 : {uint}
              16 : type
              17 : <unknown>
              18 : void
              19 : main::foo() -> void
              l0 : main::Web_Event
              l1 : <unknown>
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::UInt(0).into(),
                    },
                    488..490,
                    None,
                ),
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::Type.into(),
                    },
                    492..496,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn is_variant_directive_optional_without_type() {
    // unlike #unwrap, #is_variant requires a type argument
    check(
        r#"
            foo :: () {
                message := ?str.("hello!");

                is := #is_variant(message);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              7 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              3 : ?str
              4 : ?str
              5 : <unknown>
              6 : void
              7 : main::foo() -> void
              l0 : ?str
              l1 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MissingArg {
                    expected: ExpectedTy::Concrete(Ty::Type.into()),
                },
                111..111,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_optional_with_type_correct() {
    check(
        r#"
            foo :: () {
                message := ?str.("hello!");

                is := #is_variant(message, str);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              8 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              3 : ?str
              4 : ?str
              5 : type
              6 : bool
              7 : void
              8 : main::foo() -> void
              l0 : ?str
              l1 : bool
        "#]],
        |_| [],
    )
}

#[test]
fn is_variant_directive_optional_with_nil_correct() {
    check(
        r#"
            foo :: () {
                message := ?str.("hello!");

                is := #is_variant(message, nil);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              8 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              3 : ?str
              4 : ?str
              5 : nil
              6 : bool
              7 : void
              8 : main::foo() -> void
              l0 : ?str
              l1 : bool
        "#]],
        |_| [],
    )
}

#[test]
fn is_variant_directive_optional_with_type_incorrect() {
    check(
        r#"
            foo :: () {
                message := ?str.("hello!");

                is := #is_variant(message, i64);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              8 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              3 : ?str
              4 : ?str
              5 : type
              6 : <unknown>
              7 : void
              8 : main::foo() -> void
              l0 : ?str
              l1 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::NotAVariantOfSumType {
                    ty: Ty::IInt(64).into(),
                    sum_ty: Ty::Optional {
                        sub_ty: Ty::String.into(),
                    }
                    .into(),
                },
                113..116,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_optional_with_type_incorrect_extra_arg() {
    // todo: maybe this should show the incorrect type AND the extra args
    check(
        r#"
            foo :: () {
                message := ?str.("hello!");

                is := #is_variant(message, i64, "hello", true);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              10 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              3 : ?str
              4 : ?str
              5 : type
              6 : str
              7 : bool
              8 : <unknown>
              9 : void
              10 : main::foo() -> void
              l0 : ?str
              l1 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::NotAVariantOfSumType {
                    ty: Ty::IInt(64).into(),
                    sum_ty: Ty::Optional {
                        sub_ty: Ty::String.into(),
                    }
                    .into(),
                },
                113..116,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_optional_with_type_correct_extra_arg() {
    check(
        r#"
            foo :: () {
                message := ?str.("hello!");

                is := #is_variant(message, str, "hello", true);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              10 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : str
              3 : ?str
              4 : ?str
              5 : type
              6 : str
              7 : bool
              8 : <unknown>
              9 : void
              10 : main::foo() -> void
              l0 : ?str
              l1 : <unknown>
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::String.into(),
                    },
                    118..125,
                    None,
                ),
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::Bool.into(),
                    },
                    127..131,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn is_variant_directive_error_union_with_payload_type() {
    check(
        r#"
            foo :: () {
                result := str!u64.(42);

                is := #is_variant(result, u64);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              4 : str!u64
              5 : str!u64
              6 : type
              7 : bool
              8 : void
              9 : main::foo() -> void
              l0 : str!u64
              l1 : bool
        "#]],
        |_| [],
    )
}

#[test]
fn is_variant_directive_error_union_with_error_type() {
    // todo: {uint} should be weak replaced by u64
    check(
        r#"
            foo :: () {
                result := str!u64.(42);

                is := #is_variant(result, str);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              4 : str!u64
              5 : str!u64
              6 : type
              7 : bool
              8 : void
              9 : main::foo() -> void
              l0 : str!u64
              l1 : bool
        "#]],
        |_| [],
    )
}

#[test]
fn is_variant_directive_error_union_with_type_incorrect() {
    // todo: print a help that shows which variant you might've been referring to.
    check(
        r#"
            foo :: () {
                result := str!u64.(42);

                is := #is_variant(result, u8);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              4 : str!u64
              5 : str!u64
              6 : type
              7 : <unknown>
              8 : void
              9 : main::foo() -> void
              l0 : str!u64
              l1 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::NotAVariantOfSumType {
                    ty: Ty::UInt(8).into(),
                    sum_ty: Ty::ErrorUnion {
                        error_ty: Ty::String.into(),
                        payload_ty: Ty::UInt(64).into(),
                    }
                    .into(),
                },
                108..110,
                None,
            )]
        },
    )
}

#[test]
fn is_variant_directive_error_union_extra_arg() {
    check(
        r#"
            foo :: () {
                result := str!u64.(42);

                is := #is_variant(result, u64, "hi", true);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              4 : str!u64
              5 : str!u64
              6 : type
              7 : str
              8 : bool
              9 : <unknown>
              10 : void
              11 : main::foo() -> void
              l0 : str!u64
              l1 : <unknown>
        "#]],
        |_| {
            [
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::String.into(),
                    },
                    113..117,
                    None,
                ),
                (
                    TyDiagnosticKind::ExtraArg {
                        found: Ty::Bool.into(),
                    },
                    119..123,
                    None,
                ),
            ]
        },
    )
}

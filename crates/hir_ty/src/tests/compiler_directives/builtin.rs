use super::*;

use expect_test::expect;

#[test]
fn builtin_function() {
    check(
        r#"
            my_function :: (ptr: rawptr) -> usize #builtin("const_rawptr_to_usize");
        "#,
        expect![[r#"
            main::my_function : (rawptr) -> usize
            2 : (rawptr) -> usize
        "#]],
        |_| [],
    )
}

#[test]
fn builtin_function_wrong_params() {
    // todo: maybe change the range to the `#builtin(..)`
    check(
        r#"
            my_function :: (ptr: ?rawptr) -> usize #builtin("const_rawptr_to_usize");
        "#,
        expect![[r#"
            main::my_function : (?rawptr) -> usize
            3 : (?rawptr) -> usize
        "#]],
        |i| {
            [(
                TyDiagnosticKind::BuiltinFunctionMismatch {
                    builtin_name: i.intern("const_rawptr_to_usize"),
                    expected: Ty::Function {
                        param_tys: vec![ParamTy {
                            ty: Ty::RawPtr { mutable: false }.into(),
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::UInt(u8::MAX).into(),
                    }
                    .into(),
                    found: Ty::Function {
                        param_tys: vec![ParamTy {
                            ty: Ty::Optional {
                                sub_ty: Ty::RawPtr { mutable: false }.into(),
                            }
                            .into(),
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::UInt(u8::MAX).into(),
                    }
                    .into(),
                },
                28..85,
                None,
            )]
        },
    )
}

#[test]
fn builtin_function_wrong_ret() {
    check(
        r#"
            my_function :: (ptr: rawptr) #builtin("const_rawptr_to_usize");
        "#,
        expect![[r#"
            main::my_function : (rawptr) -> void
            1 : (rawptr) -> void
        "#]],
        |i| {
            [(
                TyDiagnosticKind::BuiltinFunctionMismatch {
                    builtin_name: i.intern("const_rawptr_to_usize"),
                    expected: Ty::Function {
                        param_tys: vec![ParamTy {
                            ty: Ty::RawPtr { mutable: false }.into(),
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::UInt(u8::MAX).into(),
                    }
                    .into(),
                    found: Ty::Function {
                        param_tys: vec![ParamTy {
                            ty: Ty::RawPtr { mutable: false }.into(),
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::Void.into(),
                    }
                    .into(),
                },
                28..75,
                None,
            )]
        },
    )
}

#[test]
fn builtin_global() {
    check(
        r#"
            Layout :: struct {
                size: usize,
                align: usize,
            };

            foo : Layout : #builtin("pointer_layout");
        "#,
        expect![[r#"
            main::Layout : type
            main::foo : main::Layout
            2 : type
            4 : str
            5 : main::Layout
        "#]],
        |_| [],
    )
}

#[test]
fn builtin_global_without_type_annotation() {
    check(
        r#"
            foo :: #builtin("pointer_layout");
        "#,
        expect![[r#"
            main::foo : ~struct {size: usize, align: usize}
            0 : str
            1 : ~struct {size: usize, align: usize}
        "#]],
        |_| [],
    )
}

#[test]
fn builtin_function_slice() {
    // todo: maybe this should get weak type replaced
    check(
        r#"
            Layout :: struct {
                size: usize,
                align: usize,
            };

            foo : [] Layout : #builtin("enum_layouts");
        "#,
        expect![[r#"
            main::Layout : type
            main::foo : []main::Layout
            2 : type
            5 : str
            6 : []main::Layout
        "#]],
        |_| [],
    )
}

#[test]
fn builtin_function_slice_wrong_fields() {
    check(
        r#"
            Layout :: struct {
                size1: usize,
                align1: usize,
            };

            foo : [] Layout : #builtin("enum_layouts");
        "#,
        expect![[r#"
            main::Layout : type
            main::foo : []main::Layout
            2 : type
            5 : str
            6 : []~struct {size: usize, align: usize}
        "#]],
        |i| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Slice {
                            sub_ty: Ty::ConcreteStruct {
                                uid: 0,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("size1")),
                                        ty: Ty::UInt(u8::MAX).into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("align1")),
                                        ty: Ty::UInt(u8::MAX).into(),
                                    },
                                ],
                            }
                            .into(),
                        }
                        .into(),
                    ),
                    found: Ty::Slice {
                        sub_ty: Ty::AnonStruct {
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("size")),
                                    ty: Ty::UInt(u8::MAX).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("align")),
                                    ty: Ty::UInt(u8::MAX).into(),
                                },
                            ],
                        }
                        .into(),
                    }
                    .into(),
                },
                139..163,
                None,
            )]
        },
    )
}

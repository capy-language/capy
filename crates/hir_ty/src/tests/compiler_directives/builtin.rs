use super::*;

use expect_test::expect;
use hir::{Expr, Lambda};
use la_arena::RawIdx;

#[test]
fn builtin_function() {
    check(
        r#"
            my_function :: (ptr: rawptr) -> usize #builtin("const_rawptr_to_usize");
        "#,
        expect![[r#"
            main::my_function : main::my_function(rawptr) -> usize
              2 : main::my_function(rawptr) -> usize
            main::lambda#my_function : ?
              2 : main::my_function(rawptr) -> usize
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
            main::my_function : main::my_function(?rawptr) -> usize
              3 : main::my_function(?rawptr) -> usize
            main::lambda#my_function : ?
              3 : main::my_function(?rawptr) -> usize
        "#]],
        |i| {
            [(
                TyDiagnosticKind::BuiltinFunctionMismatch {
                    builtin_name: i.intern("const_rawptr_to_usize"),
                    expected: Ty::FunctionPointer {
                        param_tys: vec![ParamTy {
                            ty: Ty::RawPtr { mutable: false }.into(),
                            comptime: None,
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::UInt(u8::MAX).into(),
                    }
                    .into(),
                    found: Ty::ConcreteFunction {
                        param_tys: vec![ParamTy {
                            ty: Ty::Optional {
                                sub_ty: Ty::RawPtr { mutable: false }.into(),
                            }
                            .into(),
                            comptime: None,
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::UInt(u8::MAX).into(),
                        fn_loc: NaiveLambdaLoc {
                            file: FileName(i.intern("main.capy")),
                            expr: Idx::<Expr>::from_raw(RawIdx::from_u32(3)),
                            lambda: Idx::<Lambda>::from_raw(RawIdx::from_u32(0)),
                        }
                        .make_concrete(None),
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
            main::my_function : main::my_function(rawptr) -> void
              1 : main::my_function(rawptr) -> void
            main::lambda#my_function : ?
              1 : main::my_function(rawptr) -> void
        "#]],
        |i| {
            [(
                TyDiagnosticKind::BuiltinFunctionMismatch {
                    builtin_name: i.intern("const_rawptr_to_usize"),
                    expected: Ty::FunctionPointer {
                        param_tys: vec![ParamTy {
                            ty: Ty::RawPtr { mutable: false }.into(),
                            comptime: None,
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::UInt(u8::MAX).into(),
                    }
                    .into(),
                    found: Ty::ConcreteFunction {
                        param_tys: vec![ParamTy {
                            ty: Ty::RawPtr { mutable: false }.into(),
                            comptime: None,
                            varargs: false,
                            impossible_to_differentiate: false,
                        }],
                        return_ty: Ty::Void.into(),
                        fn_loc: NaiveLambdaLoc {
                            file: FileName(i.intern("main.capy")),
                            expr: Idx::<Expr>::from_raw(RawIdx::from_u32(1)),
                            lambda: Idx::<Lambda>::from_raw(RawIdx::from_u32(0)),
                        }
                        .make_concrete(None),
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
              2 : type
            main::foo : main::Layout
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
              2 : type
            main::foo : []main::Layout
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
              2 : type
            main::foo : []main::Layout
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
                                        name: Name(i.intern("size1")),
                                        ty: Ty::UInt(u8::MAX).into(),
                                    },
                                    MemberTy {
                                        name: Name(i.intern("align1")),
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
                                    name: Name(i.intern("size")),
                                    ty: Ty::UInt(u8::MAX).into(),
                                },
                                MemberTy {
                                    name: Name(i.intern("align")),
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

use super::*;

use expect_test::expect;

#[test]
fn rawptr() {
    check(
        r#"
            get_any :: () {
                foo : i32 = 5;

                ptr : ^i32 = ^foo;
                ptr : rawptr = rawptr.(ptr);
                ptr : ^f32 = ^f32.(ptr);

                foo : f32 = ptr^;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              20 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : i32
              4 : i32
              5 : ^i32
              7 : ^i32
              9 : rawptr
              12 : rawptr
              15 : ^f32
              17 : ^f32
              18 : f32
              19 : void
              20 : main::get_any() -> void
              l0 : i32
              l1 : ^i32
              l2 : rawptr
              l3 : ^f32
              l4 : f32
        "#]],
        |_| [],
    );
}

#[test]
fn rawslice() {
    check(
        r#"
            get_any :: () {
                foo : [] i32 = i32.[100, 200];

                ptr : rawslice = rawslice.(foo);

                foo : [] f32 = []f32.(ptr);

                first : f32 = foo[0];
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              21 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              3 : i32
              4 : i32
              5 : [2]i32
              7 : []i32
              9 : rawslice
              12 : rawslice
              15 : []f32
              17 : []f32
              18 : usize
              19 : f32
              20 : void
              21 : main::get_any() -> void
              l0 : []i32
              l1 : rawslice
              l2 : []f32
              l3 : f32
        "#]],
        |_| [],
    );
}

#[test]
fn cast_ptr_without_raw() {
    check(
        r#"
            get_any :: () {
                foo : i32 = 5;

                ptr : ^i32 = ^foo;
                ptr : ^f32 = ^f32.(ptr);

                foo : f32 = ptr^;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              16 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : i32
              4 : i32
              5 : ^i32
              8 : ^i32
              11 : ^f32
              13 : ^f32
              14 : f32
              15 : void
              16 : main::get_any() -> void
              l0 : i32
              l1 : ^i32
              l2 : ^f32
              l3 : f32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Uncastable {
                    from: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                    to: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Float(32).into(),
                    }
                    .into(),
                },
                125..135,
                None,
            )]
        },
    );
}

#[test]
fn cast_slice_without_raw() {
    check(
        r#"
            get_any :: () {
                foo : [] i32 = i32.[100, 200];

                foo : [] f32 = []f32.(foo);
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              13 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              3 : i32
              4 : i32
              5 : [2]i32
              8 : []i32
              11 : []f32
              12 : void
              13 : main::get_any() -> void
              l0 : []i32
              l1 : []f32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Uncastable {
                    from: Ty::Slice {
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                    to: Ty::Slice {
                        sub_ty: Ty::Float(32).into(),
                    }
                    .into(),
                },
                108..119,
                None,
            )]
        },
    );
}

#[test]
fn deref_rawptr() {
    check(
        r#"
            get_any :: () {
                foo : i32 = 5;

                ptr : ^i32 = ^foo;
                ptr : rawptr = rawptr.(ptr);

                foo := ptr^;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              13 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : i32
              4 : i32
              5 : ^i32
              7 : ^i32
              9 : rawptr
              10 : rawptr
              11 : <unknown>
              12 : void
              13 : main::get_any() -> void
              l0 : i32
              l1 : ^i32
              l2 : rawptr
              l3 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::DerefRaw, 165..169, None)],
    );
}

#[test]
fn index_rawslice() {
    check(
        r#"
            get_any :: () {
                foo : [3] i32 = i32.[5, 10, 15];

                ptr : [] i32 = foo;
                ptr : rawslice = rawslice.(ptr);

                foo := ptr[0];
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              19 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              0 : usize
              4 : i32
              5 : i32
              6 : i32
              7 : [3]i32
              10 : [3]i32
              12 : []i32
              14 : rawslice
              15 : rawslice
              16 : usize
              17 : <unknown>
              18 : void
              19 : main::get_any() -> void
              l0 : [3]i32
              l1 : []i32
              l2 : rawslice
              l3 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::IndexRaw, 188..194, None)],
    );
}

// todo: should there be a rawarray type?
// #[test]
// fn index_any_array() {
//     check(
//         r#"
//             get_any :: (foo: [3] any) {
//                 foo : any = foo[0];
//             }
//         "#,
//         expect![[r#"
//             main::get_any : ([3]any) -> void
//             0 : usize
//             4 : [3]any
//             5 : usize
//             6 : <unknown>
//             7 : void
//             8 : ([3]any) -> void
//             l0 : any
//         "#]],
//         |_| [(TyDiagnosticKind::IndexRaw { size: Some(3) }, 77..83, None)],
//     );
// }

#[test]
fn auto_real_ptr_to_rawptr() {
    check(
        r#"
            get_any :: () {
                foo : i32 = 5;
                ptr : ^i32 = ^foo;

                ptr : rawptr = ptr;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              9 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : i32
              4 : i32
              5 : ^i32
              7 : ^i32
              8 : void
              9 : main::get_any() -> void
              l0 : i32
              l1 : ^i32
              l2 : rawptr
        "#]],
        |_| [],
    );
}

#[test]
fn auto_rawptr_to_real_ptr() {
    check(
        r#"
            get_any :: () {
                foo : i32 = 5;
                ptr : ^i32 = ^foo;
                ptr : rawptr = ptr as rawptr;

                ptr : ^i32 = ptr;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              14 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : i32
              4 : i32
              5 : ^i32
              7 : ^i32
              9 : rawptr
              12 : rawptr
              13 : void
              14 : main::get_any() -> void
              l0 : i32
              l1 : ^i32
              l2 : rawptr
              l3 : ^i32
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
                    found: Ty::RawPtr { mutable: false }.into(),
                },
                171..174,
                None,
            )]
        },
    );
}

#[test]
fn auto_real_slice_to_rawslice() {
    check(
        r#"
            get_any :: () {
                foo : [] i32 = i32.[5, 10, 15];

                ptr : rawslice = foo;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              10 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              3 : i32
              4 : i32
              5 : i32
              6 : [3]i32
              8 : []i32
              9 : void
              10 : main::get_any() -> void
              l0 : []i32
              l1 : rawslice
        "#]],
        |_| [],
    );
}

#[test]
fn auto_rawslice_to_real_slice() {
    check(
        r#"
            get_any :: () {
                foo : [] i32 = i32.[5, 10, 15];
                ptr : rawslice = rawslice.(foo);

                ptr : [] i32 = ptr;
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              15 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              3 : i32
              4 : i32
              5 : i32
              6 : [3]i32
              8 : []i32
              10 : rawslice
              13 : rawslice
              14 : void
              15 : main::get_any() -> void
              l0 : []i32
              l1 : rawslice
              l2 : []i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Slice {
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    ),
                    found: Ty::RawSlice.into(),
                },
                158..161,
                None,
            )]
        },
    );
}

#[test]
fn rawptr_to_str() {
    check(
        r#"
            get_any :: () {
                data := char.['h', 'i', '\0'];
                ptr := rawptr.(^data);
                str := str.(ptr);
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              13 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : char
              2 : char
              3 : char
              4 : [3]char
              5 : [3]char
              6 : ^[3]char
              8 : rawptr
              9 : rawptr
              11 : str
              12 : void
              13 : main::get_any() -> void
              l0 : [3]char
              l1 : rawptr
              l2 : str
        "#]],
        |_| [],
    );
}

#[test]
fn implicit_weak_ptr_to_rawptr() {
    // todo: produce a more helpful error
    check(
        r#"
            foo :: () {
                x : rawptr = ^42;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              4 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : {uint}
              2 : ^{uint}
              3 : void
              4 : main::foo() -> void
              l0 : rawptr
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::RawPtr { mutable: false }.into()),
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::UInt(0).into(),
                    }
                    .into(),
                },
                54..57,
                None,
            )]
        },
    )
}

#[test]
fn explicit_weak_ptr_to_i32_to_rawptr() {
    check(
        r#"
            foo :: () {
                x : rawptr = ^i32.(^42);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              7 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : i32
              2 : ^i32
              5 : ^i32
              6 : void
              7 : main::foo() -> void
              l0 : rawptr
        "#]],
        |_| [],
    )
}

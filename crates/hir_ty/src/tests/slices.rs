use super::*;

use expect_test::expect;

#[test]
fn slice() {
    check(
        r#"
            foo :: () {
                x : [] i32 = i32.[1, 2, 3];

                y : [] i32 = i32.[4, 6, 7, 8];
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              16 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : i32
              4 : i32
              5 : i32
              6 : [3]i32
              10 : i32
              11 : i32
              12 : i32
              13 : i32
              14 : [4]i32
              15 : void
              16 : main::foo() -> void
              l0 : []i32
              l1 : []i32
        "#]],
        |_| [],
    )
}

#[test]
fn explicit_slice_to_array() {
    check(
        r#"
            foo :: () {
                x : [] i32 = i32.[1, 2, 3];
                
                y := [3]i32.(x);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              13 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : i32
              4 : i32
              5 : i32
              6 : [3]i32
              7 : []i32
              8 : usize
              11 : [3]i32
              12 : void
              13 : main::foo() -> void
              l0 : []i32
              l1 : [3]i32
        "#]],
        |_| [],
    )
}

#[test]
fn implicit_slice_to_array() {
    check(
        r#"
            foo :: () {
                x : [] i32 = i32.[1, 2, 3];
                
                y : [3] i32 = x;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              12 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : i32
              4 : i32
              5 : i32
              6 : [3]i32
              7 : usize
              10 : []i32
              11 : void
              12 : main::foo() -> void
              l0 : []i32
              l1 : [3]i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteArray {
                            size: 3,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    ),
                    found: Ty::Slice {
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                },
                116..117,
                None,
            )]
        },
    )
}

#[test]
fn explicit_array_to_slice() {
    check(
        r#"
            foo :: () {
                x := i32.[1, 2, 3];
                
                y := []i32.(x);
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              10 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : i32
              2 : i32
              3 : i32
              4 : [3]i32
              5 : [3]i32
              8 : []i32
              9 : void
              10 : main::foo() -> void
              l0 : [3]i32
              l1 : []i32
        "#]],
        |_| [],
    )
}

#[test]
fn implicit_array_to_slice() {
    check(
        r#"
            foo :: () {
                x : [3] i32 = i32.[1, 2, 3];
                
                y : [] i32 = x;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              12 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : usize
              4 : i32
              5 : i32
              6 : i32
              7 : [3]i32
              10 : [3]i32
              11 : void
              12 : main::foo() -> void
              l0 : [3]i32
              l1 : []i32
        "#]],
        |_| [],
    )
}

#[test]
fn slice_non_distinct_fits_into_distinct() {
    check(
        r#"
            My_Type :: distinct i8;
            foo :: () {
                x : [3] i8 = i8.[1, 2, 3];

                y : []  i8 = x;
                
                z : [] My_Type = y;
            }
        "#,
        expect![[r#"
            main::My_Type : type
              1 : type
            main::foo : main::foo() -> void
              17 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              2 : usize
              6 : i8
              7 : i8
              8 : i8
              9 : [3]i8
              12 : [3]i8
              15 : []main::My_Type
              16 : void
              17 : main::foo() -> void
              l0 : [3]i8
              l1 : []i8
              l2 : []main::My_Type
        "#]],
        |_| [],
    )
}

#[test]
fn slice_distinct_fits_into_non_distinct() {
    check(
        r#"
            My_Type :: distinct i8;

            foo :: () {
                x : [3] My_Type = i8.[1, 2, 3];

                y : []  My_Type = x;
                
                z : []  i8 = y;
            }
        "#,
        expect![[r#"
            main::My_Type : type
              1 : type
            main::foo : main::foo() -> void
              17 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              2 : usize
              6 : i8
              7 : i8
              8 : i8
              9 : [3]i8
              12 : [3]main::My_Type
              15 : []main::My_Type
              16 : void
              17 : main::foo() -> void
              l0 : [3]main::My_Type
              l1 : []main::My_Type
              l2 : []i8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::Slice {
                            sub_ty: Ty::IInt(8).into(),
                        }
                        .into(),
                    ),
                    found: Ty::Slice {
                        sub_ty: Ty::Distinct {
                            uid: 0,
                            sub_ty: Ty::IInt(8).into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                194..195,
                None,
            )]
        },
    )
}

#[test]
fn slice_fits_into_mismatch() {
    check(
        r#"
            foo :: () {
                x : [3] i8 = i8.[1, 2, 3];

                y : []  i8 = x;
                
                z : [] i32 = y;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              15 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : usize
              4 : i8
              5 : i8
              6 : i8
              7 : [3]i8
              10 : [3]i8
              13 : []i8
              14 : void
              15 : main::foo() -> void
              l0 : [3]i8
              l1 : []i8
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
                    found: Ty::Slice {
                        sub_ty: Ty::IInt(8).into(),
                    }
                    .into(),
                },
                147..148,
                None,
            )]
        },
    )
}

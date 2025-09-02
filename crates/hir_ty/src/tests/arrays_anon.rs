use super::*;

use expect_test::expect;

#[test]
fn anon_array() {
    check(
        r#"
            anon :: () {
                foo := .[1, 2, 3];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : ~[3]{uint}
            4 : void
            5 : () -> void
            l0 : ~[3]{uint}
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_into_known_array() {
    check(
        r#"
            anon :: () {
                foo : [3]u16 = .[1, 2, 3];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : usize
            3 : u16
            4 : u16
            5 : u16
            6 : [3]u16
            7 : void
            8 : () -> void
            l0 : [3]u16
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_into_known_slice() {
    check(
        r#"
            anon :: () {
                foo : []u16 = .[1, 2, 3];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            2 : u16
            3 : u16
            4 : u16
            5 : [3]u16
            6 : void
            7 : () -> void
            l0 : []u16
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_as_known_array() {
    check(
        r#"
            anon :: () {
                foo := [3]u128.(.[1, 2, 3]);
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : u128
            1 : u128
            2 : u128
            3 : [3]u128
            4 : usize
            7 : [3]u128
            8 : void
            9 : () -> void
            l0 : [3]u128
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_as_known_slice() {
    check(
        r#"
            anon :: () {
                foo := []i8.(.[1, 2, 3]);
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : i8
            1 : i8
            2 : i8
            3 : [3]i8
            6 : []i8
            7 : void
            8 : () -> void
            l0 : []i8
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_into_known_array_too_large() {
    check(
        r#"
            anon :: () {
                foo : [3]i16 = .[1, 2, 3, 4];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : usize
            3 : {uint}
            4 : {uint}
            5 : {uint}
            6 : {uint}
            7 : ~[4]{uint}
            8 : void
            9 : () -> void
            l0 : [3]i16
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteArray {
                            size: 3,
                            sub_ty: Ty::IInt(16).into(),
                        }
                        .into(),
                    ),
                    found: Ty::AnonArray {
                        size: 4,
                        sub_ty: Ty::UInt(0).into(),
                    }
                    .into(),
                },
                57..70,
                None,
            )]
        },
    )
}

#[test]
fn anon_array_into_known_array_too_small() {
    check(
        r#"
            anon :: () {
                foo : [3]i16 = .[1, 2];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : usize
            3 : {uint}
            4 : {uint}
            5 : ~[2]{uint}
            6 : void
            7 : () -> void
            l0 : [3]i16
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(
                        Ty::ConcreteArray {
                            size: 3,
                            sub_ty: Ty::IInt(16).into(),
                        }
                        .into(),
                    ),
                    found: Ty::AnonArray {
                        size: 2,
                        sub_ty: Ty::UInt(0).into(),
                    }
                    .into(),
                },
                57..64,
                None,
            )]
        },
    )
}

#[test]
fn anon_array_into_known_array_by_inference() {
    check(
        r#"
            anon :: () {
                foo := .[1, 2];

                bar : [2]i128 = foo;
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : i128
            1 : i128
            2 : [2]i128
            3 : usize
            6 : [2]i128
            7 : void
            8 : () -> void
            l0 : [2]i128
            l1 : [2]i128
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_into_known_slice_by_inference() {
    check(
        r#"
            anon :: () {
                foo := .[1, 2];

                bar : []u128 = foo;
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : u128
            1 : u128
            2 : [2]u128
            5 : [2]u128
            6 : void
            7 : () -> void
            l0 : [2]u128
            l1 : []u128
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_signed_int_inner_type() {
    check(
        r#"
            anon :: () {
                foo := .[4, -5, 6];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {int}
            1 : {int}
            2 : {int}
            3 : {int}
            4 : ~[3]{int}
            5 : void
            6 : () -> void
            l0 : ~[3]{int}
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_i64_inner_type() {
    check(
        r#"
            anon :: () {
                second : i64 = 42;

                foo := .[4, second, 6];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            1 : i64
            2 : i64
            3 : i64
            4 : i64
            5 : ~[3]i64
            6 : void
            7 : () -> void
            l0 : i64
            l1 : ~[3]i64
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_i64_i128_inner_type() {
    check(
        r#"
            anon :: () {
                second : i64 = 42;
                third : i128 = 5;

                foo := .[4, second, third, 7];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            1 : i64
            3 : i128
            4 : i128
            5 : i64
            6 : i128
            7 : i128
            8 : ~[4]i128
            9 : void
            10 : () -> void
            l0 : i64
            l1 : i128
            l2 : ~[4]i128
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_mismatch_inner_types() {
    // this SHOULD return an error.
    // I think automatically casting this to any would be unexpected
    check(
        r#"
            anon :: () {
                foo := .[1, -2, true, "Hello, Sailor!", 0.1];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : {int}
            2 : {int}
            3 : bool
            4 : str
            5 : {float}
            6 : ~[5]<unknown>
            7 : void
            8 : () -> void
            l0 : ~[5]<unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::IInt(0).into()),
                    found: Ty::Bool.into(),
                },
                58..62,
                None,
            )]
        },
    )
}

#[test]
fn anon_array_index() {
    check(
        r#"
            anon :: () {
                foo := .[1, 2, 3];

                foo[1];
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : ~[3]{uint}
            4 : ~[3]{uint}
            5 : usize
            6 : {uint}
            7 : void
            8 : () -> void
            l0 : ~[3]{uint}
        "#]],
        |_| [],
    )
}

#[test]
fn anon_array_index_mutation() {
    // todo: test if `42` will get a type of `i32` when the array later becomes concrete
    check(
        r#"
            anon :: () {
                foo := .[1, 2, 3];

                foo[1] = 42;
            }
        "#,
        expect![[r#"
            main::anon : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : ~[3]{uint}
            4 : ~[3]{uint}
            5 : usize
            6 : {uint}
            7 : {uint}
            8 : void
            9 : () -> void
            l0 : ~[3]{uint}
        "#]],
        |_| [],
    )
}

use super::*;

use expect_test::expect;

#[test]
fn array() {
    check(
        r#"
            main :: () {
                my_array := i32.[4, 8, 15, 16, 23, 42];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : i32
            5 : i32
            6 : i32
            7 : [6]i32
            8 : void
            9 : () -> void
            l0 : [6]i32
        "#]],
        |_| [],
    );
}

#[test]
fn array_ty_with_size() {
    check(
        r#"
            main :: () {
                my_array : [6] i32 = i32.[1, 2, 3, 4, 5, 6];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : usize
            4 : i32
            5 : i32
            6 : i32
            7 : i32
            8 : i32
            9 : i32
            10 : [6]i32
            11 : void
            12 : () -> void
            l0 : [6]i32
        "#]],
        |_| [],
    );
}

#[test]
fn array_ty_with_global_size() {
    check(
        r#"
            size : usize : 3;

            main :: () {
                my_array : [size] i32 = i32.[1, 2, 3];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            main::size : usize
            1 : usize
            2 : usize
            6 : i32
            7 : i32
            8 : i32
            9 : [3]i32
            10 : void
            11 : () -> void
            l0 : [3]i32
        "#]],
        |_| [],
    );
}

#[test]
fn array_ty_with_imported_global_size() {
    check(
        r#"
            #- main.capy

            other :: #import("other.capy");

            main :: () {
                my_array : [other.size] bool = bool.[true, false];
            };

            #- other.capy

            size : usize : 2;
        "#,
        expect![[r#"
            main::main : () -> void
            main::other : file other
            other::size : usize
            other:
              1 : usize
            main:
              0 : file other
              1 : file other
              2 : usize
              6 : bool
              7 : bool
              8 : [2]bool
              9 : void
              10 : () -> void
              l0 : [2]bool
        "#]],
        |_| [],
    );
}

#[test]
fn array_ty_with_extern_global_size() {
    check(
        r#"
            size : usize : extern;

            main :: () {
                my_array : [size] i32 = i32.[];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            main::size : usize
            1 : usize
            5 : [0]i32
            6 : void
            7 : () -> void
            l0 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::ArraySizeNotConst, 90..94, None)],
    );
}

#[test]
fn array_ty_with_extern_imported_global_size() {
    check(
        r#"
            #- main.capy

            other :: #import("other.capy");

            main :: () {
                my_array : [other.size] bool = bool.[];
            };

            #- other.capy

            size : usize : extern;
        "#,
        expect![[r#"
            main::main : () -> void
            main::other : file other
            other::size : usize
            other:
            main:
              0 : file other
              1 : file other
              2 : usize
              6 : [0]bool
              7 : void
              8 : () -> void
              l0 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::ArraySizeNotConst, 99..109, None)],
    );
}

#[test]
fn array_ty_with_extern_global_through_regular_global_size() {
    // I'm testing multiple things at once here.

    // todo: ArraySizeNotConst should come with a help diag explaining why just like CannotMutate
    check(
        r#"
            foo : usize : extern;

            bar :: foo;

            main :: () {
                my_array : [bar] i32 = i32.[];
            };
        "#,
        expect![[r#"
            main::bar : usize
            main::foo : usize
            main::main : () -> void
            1 : usize
            2 : usize
            6 : [0]i32
            7 : void
            8 : () -> void
            l0 : <unknown>
        "#]],
        |_| {
            [
                (TyDiagnosticKind::GlobalNotConst, 55..58, None),
                (TyDiagnosticKind::ArraySizeNotConst, 114..117, None),
            ]
        },
    );
}

#[test]
fn array_ty_with_float_size() {
    check(
        r#"
            main :: () {
                my_array : [1.0] i32 = i32.[1];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {float}
            4 : i32
            5 : [1]i32
            6 : void
            7 : () -> void
            l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(u8::MAX).into()),
                    found: Ty::Float(0).into(),
                },
                54..57,
                None,
            )]
        },
    );
}

#[test]
fn array_ty_with_local_size() {
    check(
        r#"
            main :: () {
                size :: 4;

                my_array : [size] i32 = i32.[1, 2, 3, 4];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : usize
            1 : usize
            5 : i32
            6 : i32
            7 : i32
            8 : i32
            9 : [4]i32
            10 : void
            11 : () -> void
            l0 : usize
            l1 : [4]i32
        "#]],
        |_| [],
    );
}

#[test]
fn array_ty_with_non_const_size() {
    check(
        r#"
            main :: () {
                size := 3;

                size = size + 1;

                my_array : [size] i32 = i32.[1, 2, 3, 4];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : usize
            1 : usize
            2 : usize
            3 : usize
            4 : usize
            5 : usize
            9 : i32
            10 : i32
            11 : i32
            12 : i32
            13 : [4]i32
            14 : void
            15 : () -> void
            l0 : usize
            l1 : <unknown>
        "#]],
        |_| [(TyDiagnosticKind::ArraySizeNotConst, 116..120, None)],
    );
}

#[test]
fn array_ty_with_comptime_size() {
    check(
        r#"
            main :: () {
                size :: comptime {
                    if true {
                        5
                    } else {
                        6
                    }
                };

                my_array : [size] i64 = i64.[1, 2, 3, 4, 5];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : bool
            1 : usize
            2 : usize
            3 : usize
            4 : usize
            5 : usize
            6 : usize
            7 : usize
            8 : usize
            12 : i64
            13 : i64
            14 : i64
            15 : i64
            16 : i64
            17 : [5]i64
            18 : void
            19 : () -> void
            l0 : usize
            l1 : [5]i64
        "#]],
        |_| [],
    );
}

#[test]
fn array_ty_with_negative_size() {
    check(
        r#"
            main :: () {
                my_array : [-3] i32 = i32.[];
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {int}
            1 : {int}
            5 : [0]i32
            6 : void
            7 : () -> void
            l0 : <unknown>
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(u8::MAX).into()),
                    found: Ty::IInt(0).into(),
                },
                54..56,
                None,
            )]
        },
    );
}

#[test]
fn index() {
    check(
        r#"
            main :: () -> i32 {
                my_array := i32.[4, 8, 15, 16, 23, 42];

                my_array[2]
            };
        "#,
        expect![[r#"
            main::main : () -> i32
            2 : i32
            3 : i32
            4 : i32
            5 : i32
            6 : i32
            7 : i32
            8 : [6]i32
            9 : [6]i32
            10 : usize
            11 : i32
            12 : i32
            13 : () -> i32
            l0 : [6]i32
        "#]],
        |_| [],
    );
}

#[test]
fn index_too_large() {
    check(
        r#"
            main :: () -> i32 {
                my_array := i32.[4, 8, 15, 16, 23, 42];

                my_array[1000]
            };
        "#,
        expect![[r#"
            main::main : () -> i32
            2 : i32
            3 : i32
            4 : i32
            5 : i32
            6 : i32
            7 : i32
            8 : [6]i32
            9 : [6]i32
            10 : usize
            11 : i32
            12 : i32
            13 : () -> i32
            l0 : [6]i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IndexOutOfBounds {
                    index: 1000,
                    actual_size: 6,
                    array_ty: Ty::ConcreteArray {
                        size: 6,
                        sub_ty: Ty::IInt(32).into(),
                    }
                    .into(),
                },
                106..120,
                None,
            )]
        },
    );
}

#[test]
fn index_non_array() {
    check(
        r#"
            foo :: () {
                bar := "Hello!";

                bar[0];
            };
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : str
            1 : str
            2 : usize
            3 : <unknown>
            4 : void
            5 : () -> void
            l0 : str
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IndexNonArray {
                    found: Ty::String.into(),
                },
                75..81,
                None,
            )]
        },
    );
}

#[test]
fn index_of_array_ptr() {
    check(
        r#"
            main :: () {
                arr := i32.[1, 2, 3];

                ptr := ^arr;

                ptr[0];
            }
        "#,
        expect![[r#"
            main::main : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : ^[3]i32
            7 : ^[3]i32
            8 : usize
            9 : i32
            10 : void
            11 : () -> void
            l0 : [3]i32
            l1 : ^[3]i32
        "#]],
        |_| [],
    );
}

#[test]
fn index_of_array_ptr_ptr() {
    check(
        r#"
            main :: () {
                arr := i32.[1, 2, 3];

                ptr := ^^arr;

                ptr[0];
            }
        "#,
        expect![[r#"
            main::main : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : ^[3]i32
            7 : ^^[3]i32
            8 : ^^[3]i32
            9 : usize
            10 : i32
            11 : void
            12 : () -> void
            l0 : [3]i32
            l1 : ^^[3]i32
        "#]],
        |_| [],
    );
}

#[test]
fn index_of_non_array_ptr_ptr() {
    check(
        r#"
            main :: () {
                arr := 5;

                ptr := ^^arr;

                ptr[0];
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^{uint}
            3 : ^^{uint}
            4 : ^^{uint}
            5 : usize
            6 : <unknown>
            7 : void
            8 : () -> void
            l0 : {uint}
            l1 : ^^{uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IndexNonArray {
                    found: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                100..106,
                None,
            )]
        },
    );
}

#[test]
fn index_too_large_of_array_ptr_ptr() {
    check(
        r#"
            main :: () {
                arr := i32.[1, 2, 3];

                ptr := ^^arr;

                ptr[10];
            }
        "#,
        expect![[r#"
            main::main : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : ^[3]i32
            7 : ^^[3]i32
            8 : ^^[3]i32
            9 : usize
            10 : i32
            11 : void
            12 : () -> void
            l0 : [3]i32
            l1 : ^^[3]i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IndexOutOfBounds {
                    index: 10,
                    actual_size: 3,
                    array_ty: Ty::Pointer {
                        mutable: false,
                        sub_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::ConcreteArray {
                                size: 3,
                                sub_ty: Ty::IInt(32).into(),
                            }
                            .into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                112..119,
                None,
            )]
        },
    );
}

#[test]
fn mutable_index_of_array_ptr_ptr() {
    check(
        r#"
            main :: () {
                arr := i32.[1, 2, 3];

                ptr :: ^mut ^mut arr;

                ptr[1] = 50;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : ^mut [3]i32
            7 : ^mut ^mut [3]i32
            8 : ^mut ^mut [3]i32
            9 : usize
            10 : i32
            11 : i32
            12 : void
            13 : () -> void
            l0 : [3]i32
            l1 : ^mut ^mut [3]i32
        "#]],
        |_| [],
    );
}

#[test]
fn immutable_index_of_array_ptr_ptr() {
    check(
        r#"
            main :: () {
                arr :: i32.[1, 2, 3];

                ptr := ^^arr;

                ptr[1] = 50;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : ^[3]i32
            7 : ^^[3]i32
            8 : ^^[3]i32
            9 : usize
            10 : i32
            11 : {uint}
            12 : void
            13 : () -> void
            l0 : [3]i32
            l1 : ^^[3]i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                112..124,
                Some((TyDiagnosticHelpKind::ImmutableRef, 88..93)),
            )]
        },
    );
}

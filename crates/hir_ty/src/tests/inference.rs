use super::*;

use expect_test::expect;

#[test]
fn strong_int_to_float() {
    check(
        r#"
            main :: () {
                foo : u16 = 5;

                bar : f32 = foo;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              5 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : u16
              3 : u16
              4 : void
              5 : main::main() -> void
              l0 : u16
              l1 : f32
        "#]],
        |_| [],
    );
}

#[test]
fn weak_int_to_float() {
    check(
        r#"
            main :: () {
                foo : f32 = 5;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              3 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : f32
              2 : void
              3 : main::main() -> void
              l0 : f32
        "#]],
        |_| [],
    );
}

#[test]
fn inference_simple_by_annotation() {
    check(
        r#"
            main :: () {
                num1 := 5;
                num2 := num1;
                num3 : usize = num2;
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              5 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : usize
              1 : usize
              3 : usize
              4 : void
              5 : main::main() -> void
              l0 : usize
              l1 : usize
              l2 : usize
        "#]],
        |_| [],
    );
}

#[test]
fn inference_complex_by_annotation() {
    check(
        r#"
            main :: () {
                num: i16 = {
                    res := 23;
                    if true {
                        res
                    } else {
                        -42
                    }
                };
            };
        "#,
        expect![[r#"
            main::main : main::main() -> void
              11 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : i16
              2 : bool
              3 : i16
              4 : i16
              5 : i16
              6 : i16
              7 : i16
              8 : i16
              9 : i16
              10 : void
              11 : main::main() -> void
              l0 : i16
              l1 : i16
        "#]],
        |_| [],
    );
}

#[test]
fn inference_simple_by_return() {
    check(
        r#"
            main :: () -> usize {
                num1 := 5;
                num2 := num1;
                num2
            };
        "#,
        expect![[r#"
            main::main : main::main() -> usize
              5 : main::main() -> usize
            main::lambda#main : main::main() -> usize
              1 : usize
              2 : usize
              3 : usize
              4 : usize
              5 : main::main() -> usize
              l0 : usize
              l1 : usize
        "#]],
        |_| [],
    );
}

#[test]
fn inference_complex_by_return_ok() {
    check(
        r#"
            main :: () -> i8 {
                num := {
                    res := 23;
                    if true {
                        res
                    } else {
                        -42
                    }
                };
                num
            };
        "#,
        expect![[r#"
            main::main : main::main() -> i8
              12 : main::main() -> i8
            main::lambda#main : main::main() -> i8
              1 : i8
              2 : bool
              3 : i8
              4 : i8
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : i8
              10 : i8
              11 : i8
              12 : main::main() -> i8
              l0 : i8
              l1 : i8
        "#]],
        |_| [],
    );
}

#[test]
fn inference_complex_by_return_err() {
    check(
        r#"
            main :: () -> u8 {
                num := {
                    res := 23;
                    if true {
                        res
                    } else {
                        -42
                    }
                };
                num
            };
        "#,
        expect![[r#"
            main::main : main::main() -> u8
              12 : main::main() -> u8
            main::lambda#main : main::main() -> u8
              1 : {int}
              2 : bool
              3 : {int}
              4 : {int}
              5 : {int}
              6 : {int}
              7 : {int}
              8 : {int}
              9 : {int}
              10 : {int}
              11 : <unknown>
              12 : main::main() -> u8
              l0 : {int}
              l1 : {int}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                    found: Ty::IInt(0).into(),
                },
                260..263,
                Some((
                    TyDiagnosticHelpKind::ReturnTyHere {
                        ty: Ty::UInt(8).into(),
                        is_default: false,
                    },
                    27..29,
                )),
            )]
        },
    );
}

#[test]
fn local_auto_small_to_big_same_sign() {
    check(
        r#"
            foo :: () -> i16 {
                small: i8 = 42;
                big: i16 = small;
                big
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> i16
              7 : main::foo() -> i16
            main::lambda#foo : main::foo() -> i16
              2 : i8
              4 : i8
              5 : i16
              6 : i16
              7 : main::foo() -> i16
              l0 : i8
              l1 : i16
        "#]],
        |_| [],
    );
}

#[test]
fn local_auto_big_to_small_same_sign() {
    check(
        r#"
            foo :: () -> u8 {
                big: u16 = 42;
                small: u8 = big;
                small
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> u8
              7 : main::foo() -> u8
            main::lambda#foo : main::foo() -> u8
              2 : u16
              4 : u16
              5 : u8
              6 : u8
              7 : main::foo() -> u8
              l0 : u16
              l1 : u8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                    found: Ty::UInt(16).into(),
                },
                90..93,
                None,
            )]
        },
    );
}

#[test]
fn local_auto_small_unsigned_to_big_signed() {
    check(
        r#"
            foo :: () -> i16 {
                small: u8 = 42;
                big: i16 = small;
                big
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> i16
              7 : main::foo() -> i16
            main::lambda#foo : main::foo() -> i16
              2 : u8
              4 : u8
              5 : i16
              6 : i16
              7 : main::foo() -> i16
              l0 : u8
              l1 : i16
        "#]],
        |_| [],
    );
}

#[test]
fn local_auto_small_signed_to_big_unsigned() {
    check(
        r#"
            foo :: () -> u16 {
                small: i8 = 42;
                big: u16 = small;
                big
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> u16
              7 : main::foo() -> u16
            main::lambda#foo : main::foo() -> u16
              2 : i8
              4 : i8
              5 : u16
              6 : u16
              7 : main::foo() -> u16
              l0 : i8
              l1 : u16
        "#]],
        |_| {
            // should fail due to loss of sign
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(16).into()),
                    found: Ty::IInt(8).into(),
                },
                91..96,
                None,
            )]
        },
    );
}

#[test]
fn local_auto_signed_to_unsigned() {
    check(
        r#"
            foo :: () -> u16 {
                sign: i16 = 42;
                nada: u16 = sign;
                nada
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> u16
              7 : main::foo() -> u16
            main::lambda#foo : main::foo() -> u16
              2 : i16
              4 : i16
              5 : u16
              6 : u16
              7 : main::foo() -> u16
              l0 : i16
              l1 : u16
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(16).into()),
                    found: Ty::IInt(16).into(),
                },
                92..96,
                None,
            )]
        },
    );
}

#[test]
fn local_auto_big_signed_to_small_unsigned() {
    check(
        r#"
            foo :: () -> u8 {
                big: i16 = 42;
                small: u8 = big;
                small
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> u8
              7 : main::foo() -> u8
            main::lambda#foo : main::foo() -> u8
              2 : i16
              4 : i16
              5 : u8
              6 : u8
              7 : main::foo() -> u8
              l0 : i16
              l1 : u8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                    found: Ty::IInt(16).into(),
                },
                90..93,
                None,
            )]
        },
    );
}

#[test]
fn reinfer_usages() {
    check(
        r#"
            main :: () {
                foo := 5;
            
                baz := foo;
            
                foo = foo + 1;
            
                bar(foo);
            };
            
            bar :: (x: usize) {};
        "#,
        expect![[r#"
            main::main : main::main() -> void
              10 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : usize
              1 : usize
              2 : usize
              3 : usize
              4 : usize
              5 : usize
              6 : main::bar(usize) -> void
              7 : usize
              8 : void
              9 : void
              10 : main::main() -> void
              l0 : usize
              l1 : usize
            main::bar : main::bar(usize) -> void
              13 : main::bar(usize) -> void
            main::lambda#bar : main::bar(usize) -> void
              12 : void
              13 : main::bar(usize) -> void
        "#]],
        |_| [],
    );
}

#[test]
fn reinfer_params() {
    // usually an argument will replace the weak type of a variable.
    // in this case it doesn't and so more advanced replacing is needed.
    // todo: make sure the test is still testing for what it was testing for
    check(
        r#"
            accept_any :: (val: any) {}
            
            foo :: () {
                x := 0;
                accept_any(x);
                i16.(x);
            }
        "#,
        expect![[r#"
            main::accept_any : main::accept_any(any) -> void
              2 : main::accept_any(any) -> void
            main::lambda#accept_any : main::accept_any(any) -> void
              1 : void
              2 : main::accept_any(any) -> void
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              3 : i16
              4 : main::accept_any(any) -> void
              5 : i16
              6 : void
              7 : i16
              9 : i16
              10 : void
              11 : main::foo() -> void
              l0 : i16
        "#]],
        |_| [],
    )
}

#[test]
fn weak_to_strong_u8_array_of_arrays() {
    // check for https://github.com/capy-language/capy/issues/30
    check(
        r#"
            main :: () {
                x : u8 = 1;
                y : u8 = 2;
                z : u8 = 3;

                arr : [3][3][3]u8 = .[
                    .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                    .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                    .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                ];
            }
        "#,
        expect![[r#"
            main::main : main::main() -> void
              54 : main::main() -> void
            main::lambda#main : main::main() -> void
              1 : u8
              3 : u8
              5 : u8
              6 : usize
              7 : usize
              8 : usize
              13 : u8
              14 : u8
              15 : u8
              16 : [3]u8
              17 : u8
              18 : u8
              19 : u8
              20 : [3]u8
              21 : u8
              22 : u8
              23 : u8
              24 : [3]u8
              25 : [3][3]u8
              26 : u8
              27 : u8
              28 : u8
              29 : [3]u8
              30 : u8
              31 : u8
              32 : u8
              33 : [3]u8
              34 : u8
              35 : u8
              36 : u8
              37 : [3]u8
              38 : [3][3]u8
              39 : u8
              40 : u8
              41 : u8
              42 : [3]u8
              43 : u8
              44 : u8
              45 : u8
              46 : [3]u8
              47 : u8
              48 : u8
              49 : u8
              50 : [3]u8
              51 : [3][3]u8
              52 : [3][3][3]u8
              53 : void
              54 : main::main() -> void
              l0 : u8
              l1 : u8
              l2 : u8
              l3 : [3][3][3]u8
        "#]],
        |_| [],
    )
}

#[test]
fn weak_to_strong_uint_array_of_arrays() {
    // check for https://github.com/capy-language/capy/issues/30
    check(
        r#"
            main :: () {
                x := 1;
                y := 2;
                z := 3;

                arr : [3][3][3]u8 = .[
                    .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                    .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                    .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                ];
            }
        "#,
        expect![[r#"
            main::main : main::main() -> void
              51 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : u8
              1 : u8
              2 : u8
              3 : usize
              4 : usize
              5 : usize
              10 : u8
              11 : u8
              12 : u8
              13 : [3]u8
              14 : u8
              15 : u8
              16 : u8
              17 : [3]u8
              18 : u8
              19 : u8
              20 : u8
              21 : [3]u8
              22 : [3][3]u8
              23 : u8
              24 : u8
              25 : u8
              26 : [3]u8
              27 : u8
              28 : u8
              29 : u8
              30 : [3]u8
              31 : u8
              32 : u8
              33 : u8
              34 : [3]u8
              35 : [3][3]u8
              36 : u8
              37 : u8
              38 : u8
              39 : [3]u8
              40 : u8
              41 : u8
              42 : u8
              43 : [3]u8
              44 : u8
              45 : u8
              46 : u8
              47 : [3]u8
              48 : [3][3]u8
              49 : [3][3][3]u8
              50 : void
              51 : main::main() -> void
              l0 : u8
              l1 : u8
              l2 : u8
              l3 : [3][3][3]u8
        "#]],
        |_| [],
    )
}

#[test]
fn reinfer_final_usages() {
    // check for https://github.com/capy-language/capy/issues/41
    //
    // this was essentially caused by the fact that `i` actually doesn't have a type until the
    // very very end, where in `finish_body` it gets weak type replaced by u64--but what was
    // going wrong was that before the type was getting weak type replaced, all the local
    // usages were being cleared, making it impossible for them to ALSO get weak type replaced.
    // this is fixed now.
    check(
        r#"
            log2_u64 :: (n: u64) -> u64 {
                n := n;
                i := 0;
                while n != 0 {
                    n = n << 1;
                    i = i + 1;
                }
                i
            }
        "#,
        expect![[r#"
            main::log2_u64 : main::log2_u64(u64) -> u64
              19 : main::log2_u64(u64) -> u64
            main::lambda#log2_u64 : main::log2_u64(u64) -> u64
              2 : u64
              3 : u64
              4 : u64
              5 : u64
              6 : bool
              7 : u64
              8 : u64
              9 : u64
              10 : u64
              11 : u64
              12 : u64
              13 : u64
              14 : u64
              15 : void
              16 : void
              17 : u64
              18 : u64
              19 : main::log2_u64(u64) -> u64
              l0 : u64
              l1 : u64
        "#]],
        |_| [],
    )
}

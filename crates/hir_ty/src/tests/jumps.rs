use super::*;

use expect_test::expect;

#[test]
fn break_void_block_no_tail_match() {
    check(
        r#"
            foo :: () {
                `blk: {
                    break;
                    break {};
                    break {};
                }               
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              4 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : void
              1 : void
              2 : void
              3 : void
              4 : main::foo() -> void
        "#]],
        |_| [],
    )
}

#[test]
fn break_i32_block_no_tail_mismatch() {
    check(
        r#"
            foo :: () {
                `blk: {
                    break 123;
                    break {};
                    break true;
                }               
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              5 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : void
              2 : bool
              3 : <unknown>
              4 : <unknown>
              5 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(0).into()),
                    found: Ty::Void.into(),
                },
                106..108,
                Some((
                    TyDiagnosticHelpKind::BreakHere {
                        ty: Ty::UInt(0).into(),
                        is_default: false,
                    },
                    69..79,
                )),
            )]
        },
    )
}

#[test]
fn break_i32_block_tail_match() {
    check(
        r#"
            foo :: () -> i32 {
                `blk: {
                    break 123;
                    42
                }               
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              5 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : i32
              2 : i32
              3 : i32
              4 : i32
              5 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_void_block_tail_mismatch() {
    check(
        r#"
            foo :: () {
                `blk: {
                    break {};
                    42
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              4 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : void
              1 : {uint}
              2 : <unknown>
              3 : <unknown>
              4 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Void.into()),
                    found: Ty::UInt(0).into(),
                },
                99..101,
                Some((
                    TyDiagnosticHelpKind::BreakHere {
                        ty: Ty::Void.into(),
                        is_default: false,
                    },
                    69..78,
                )),
            )]
        },
    )
}

#[test]
fn break_i32_block_from_inner() {
    check(
        r#"
            foo :: () {
                `blk: {
                    {
                        break `blk {};
                    }

                    42
                }               
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              5 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : void
              1 : noeval
              2 : {uint}
              3 : <unknown>
              4 : <unknown>
              5 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Void.into()),
                    found: Ty::UInt(0).into(),
                },
                153..155,
                Some((
                    TyDiagnosticHelpKind::BreakHere {
                        ty: Ty::Void.into(),
                        is_default: false,
                    },
                    95..109,
                )),
            )]
        },
    )
}

#[test]
fn break_i32_block_from_inner_tail() {
    check(
        r#"
        foo :: () -> i32 {
            `blk: {
                {
                    break `blk true;
                    break 5;
                    42
                }
            }
        }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              7 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : bool
              2 : {uint}
              3 : {uint}
              4 : {uint}
              5 : <unknown>
              6 : <unknown>
              7 : main::foo() -> i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Bool.into()),
                    found: Ty::UInt(0).into(),
                },
                129..130,
                Some((
                    TyDiagnosticHelpKind::BreakHere {
                        ty: Ty::Bool.into(),
                        is_default: false,
                    },
                    86..102,
                )),
            )]
        },
    )
}

#[test]
fn break_unknown_label() {
    check(
        r#"
            foo :: () {
                break `blk 42;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              2 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : void
              2 : main::foo() -> void
        "#]],
        |_| [],
    )
}

#[test]
fn return_match() {
    check(
        r#"
            foo :: () -> i32 {
                return 100;
                42
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              4 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : i32
              2 : i32
              3 : i32
              4 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn return_mismatch() {
    check(
        r#"
            foo :: () -> i32 {
                return "hello";
                42
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              4 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : str
              2 : {uint}
              3 : <unknown>
              4 : main::foo() -> i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                    found: Ty::String.into(),
                },
                55..62,
                Some((
                    TyDiagnosticHelpKind::ReturnTyHere {
                        ty: Ty::IInt(32).into(),
                        is_default: false,
                    },
                    26..29,
                )),
            )]
        },
    )
}

#[test]
fn return_only() {
    check(
        r#"
            foo :: () -> i32 {
                return 42;
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              3 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : i32
              2 : i32
              3 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn return_with_globals() {
    check(
        r#"
            a :: 42;
            b :: comptime a;
            c :: comptime b;
            d :: comptime c;

            foo :: () -> i32 {
                return 42;
                d;
                return 5;
            }
        "#,
        expect![[r#"
            main::a : i32
              0 : i32
            main::b : i32
              1 : i32
              2 : i32
            main::c : i32
              3 : i32
              4 : i32
            main::d : i32
              5 : i32
              6 : i32
            main::foo : main::foo() -> i32
              12 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              8 : i32
              9 : i32
              10 : i32
              11 : i32
              12 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_from_loop() {
    check(
        r#"
            foo :: () {
                `my_loop: loop {
                    break `my_loop;
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              3 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : noeval
              1 : void
              2 : void
              3 : main::foo() -> void
        "#]],
        |_| [],
    )
}

#[test]
fn break_from_loop_with_value() {
    check(
        r#"
            foo :: () -> i32 {
                `my_loop: loop {
                    break `my_loop 42;
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              5 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : i32
              2 : noeval
              3 : i32
              4 : i32
              5 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_from_loop_with_multiple_values() {
    check(
        r#"
            foo :: () {
                loop {
                    x : i16 = 42;
                    break x;

                    break 15;

                    x : i32 = 23;
                    break x;
                };
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              10 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : i16
              2 : i16
              3 : i16
              5 : i32
              6 : i32
              7 : noeval
              8 : i32
              9 : void
              10 : main::foo() -> void
              l0 : i16
              l1 : i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_from_while() {
    check(
        r#"
            foo :: () {
                `my_loop: while 2 + 2 == 4 {
                    break `my_loop;
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              8 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : {uint}
              3 : {uint}
              4 : bool
              5 : noeval
              6 : void
              7 : void
              8 : main::foo() -> void
        "#]],
        |_| [],
    )
}

#[test]
fn break_from_while_with_void() {
    check(
        r#"
            foo :: () {
                `my_loop: while 2 + 2 == 4 {
                    break `my_loop {};
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : {uint}
              3 : {uint}
              4 : bool
              5 : void
              6 : noeval
              7 : void
              8 : void
              9 : main::foo() -> void
        "#]],
        |_| [],
    )
}

#[test]
fn break_from_while_with_value() {
    // todo: print help diag of why void is expected
    check(
        r#"
            foo :: () {
                `my_loop: while 2 + 2 == 4 {
                    break `my_loop 42;
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              9 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : {uint}
              3 : {uint}
              4 : bool
              5 : {uint}
              6 : noeval
              7 : <unknown>
              8 : <unknown>
              9 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Void.into()),
                    found: Ty::UInt(0).into(),
                },
                105..107,
                None,
            )]
        },
    )
}

#[test]
fn continue_works() {
    check(
        r#"
            foo :: () -> i32 {
                loop {
                    continue;
                }
                42
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              5 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : noeval
              2 : void
              3 : i32
              4 : i32
              5 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_inner_if_no_else() {
    check(
        r#"
            foo :: () -> i32 {
                {
                    if true {
                        return 123;
                    }
                }

                0
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              8 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : bool
              2 : i32
              3 : noeval
              4 : void
              5 : void
              6 : i32
              7 : i32
              8 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_inner_if_with_else_no_break() {
    check(
        r#"
            foo :: () -> i32 {
                {
                    if true {
                        return 123;
                    } else {

                    }
                }

                0
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              9 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : bool
              2 : i32
              3 : noeval
              4 : void
              5 : void
              6 : void
              7 : i32
              8 : i32
              9 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn break_inner_if_with_else_break() {
    check(
        r#"
            foo :: () -> i32 {
                {
                    if true {
                        return 123;
                    } else {
                        return 456;
                    }
                }

                0
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> i32
              10 : main::foo() -> i32
            main::lambda#foo : main::foo() -> i32
              1 : bool
              2 : i32
              3 : noeval
              4 : i32
              5 : noeval
              6 : noeval
              7 : noeval
              8 : i32
              9 : i32
              10 : main::foo() -> i32
        "#]],
        |_| [],
    )
}

#[test]
fn reinfer_break_usages() {
    check(
        r#"
            foo :: () {
                `blk: {
                    x := 0;
                    break x;
                    y : i8 = x;
                };
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : i8
              1 : i8
              3 : i8
              4 : i8
              5 : void
              6 : main::foo() -> void
              l0 : i8
              l1 : i8
        "#]],
        |_| [],
    )
}

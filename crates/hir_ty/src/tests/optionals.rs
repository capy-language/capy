use super::*;

use expect_test::expect;

#[test]
fn option_assign_nil() {
    check(
        r#"
            main :: () {
                foo : ?u64 = nil;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            2 : nil
            3 : void
            4 : () -> void
            l0 : ?u64
        "#]],
        |_| [],
    )
}

#[test]
fn option_assign_value() {
    check(
        r#"
            main :: () {
                foo : ?u64 = 42;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            2 : u64
            3 : void
            4 : () -> void
            l0 : ?u64
        "#]],
        |_| [],
    )
}

#[test]
fn option_value_or_nil() {
    check(
        r#"
            main :: () {
                if true {
                    42
                } else {
                    nil
                };
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : bool
            1 : {uint}
            2 : {uint}
            3 : nil
            4 : nil
            5 : ?{uint}
            6 : void
            7 : () -> void
        "#]],
        |_| [],
    )
}

// todo: this should be u64
#[test]
fn option_infer() {
    check(
        r#"
            main :: () {
                x := 42;
                y := x;
                z := y;

                foo : ?u64 = z;
            }
        "#,
        expect![[r#"
            main::main : () -> void
            0 : u64
            1 : u64
            2 : u64
            5 : u64
            6 : void
            7 : () -> void
            l0 : u64
            l1 : u64
            l2 : u64
            l3 : ?u64
        "#]],
        |_| [],
    )
}

#[test]
fn option_from_nothing() {
    check(
        r#"
            walrus :: () -> ?void {}
        "#,
        expect![[r#"
            main::walrus : () -> ?void
            2 : ?void
            3 : () -> ?void
        "#]],
        |_| [],
    )
}

#[test]
fn option_try() {
    check(
        r#"
            walrus :: () -> ?void {
                foo : ?u64 = nil;

                foo.try;
            }
        "#,
        expect![[r#"
            main::walrus : () -> ?void
            4 : nil
            5 : ?u64
            6 : u64
            7 : ?void
            8 : () -> ?void
            l0 : ?u64
        "#]],
        |_| [],
    )
}

#[test]
fn option_compare() {
    check(
        r#"
            walrus :: () -> bool {
                foo : ?u64 = nil;

                foo == nil
            }
        "#,
        expect![[r#"
            main::walrus : () -> bool
            3 : nil
            4 : ?u64
            5 : nil
            6 : bool
            7 : bool
            8 : () -> bool
            l0 : ?u64
        "#]],
        |_| [],
    )
}

#[test]
fn try_different_payloads() {
    check(
        r#"
            foo :: () -> ?i64 {
                if bar().try {
                    // do stuff
                }

                message := baz().try;

                0
            }

            bar :: () -> ?bool {
                nil
            }

            baz :: () -> ?str {
                nil
            }
        "#,
        expect![[r#"
            main::bar : () -> ?bool
            main::baz : () -> ?str
            main::foo : () -> ?i64
            2 : () -> ?bool
            3 : ?bool
            4 : bool
            5 : void
            6 : void
            7 : () -> ?str
            8 : ?str
            9 : str
            10 : i64
            11 : ?i64
            12 : () -> ?i64
            15 : nil
            16 : ?bool
            17 : () -> ?bool
            20 : nil
            21 : ?str
            22 : () -> ?str
            l0 : str
        "#]],
        |_| [],
    )
}

#[test]
fn try_always_nil() {
    // while the side effects will still get compiled, foo is always a zero-sized type and so
    // doesn't
    check(
        r#"
            foo :: {
                ?bool.(true).try;
                ?u64.(42).try;
                ?str.("hello").try;

                nil
            };
        "#,
        expect![[r#"
            main::foo : nil
            0 : bool
            3 : ?bool
            4 : bool
            5 : u64
            8 : ?u64
            9 : u64
            10 : str
            13 : ?str
            14 : str
            15 : nil
            16 : nil
        "#]],
        // we get a global not const error but idc about that
        // that's not what the test is for
        |_| [(TyDiagnosticKind::GlobalNotConst, 20..157, None)],
    )
}

#[test]
fn switch_optional() {
    check(
        r#"
        foo :: () {
            switch inner in ?i64.(42) {
                i64 => {
                    inner;
                },
                nil => {
                    inner;
                },
            }
        }
    "#,
        expect![[r#"
            main::foo : () -> void
            0 : i64
            3 : ?i64
            4 : type
            5 : i64
            6 : void
            7 : nil
            8 : nil
            9 : void
            10 : void
            11 : void
            12 : () -> void
        "#]],
        |_| [],
    )
}

#[test]
fn switch_optional_extra_arms() {
    check(
        r#"
            foo :: () {
                switch inner in ?i64.(42) {
                    i64 => {
                        inner;
                    },
                    nil => {
                        inner;
                    },
                    str => {
                        inner;
                    },
                }
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : i64
            3 : ?i64
            4 : type
            5 : i64
            6 : void
            7 : nil
            8 : nil
            9 : void
            10 : type
            11 : str
            12 : void
            13 : <unknown>
            14 : <unknown>
            15 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::NotAVariantOfSumType {
                    ty: Ty::String.into(),
                    sum_ty: Ty::Optional {
                        sub_ty: Ty::IInt(64).into(),
                    }
                    .into(),
                },
                255..258,
                None,
            )]
        },
    )
}

#[test]
fn switch_optional_missing_arms() {
    check(
        r#"
        foo :: () {
            switch inner in ?i64.(42) {
                i64 => {
                    inner;
                },
            }
        }
    "#,
        expect![[r#"
            main::foo : () -> void
            0 : i64
            3 : ?i64
            4 : type
            5 : i64
            6 : void
            7 : void
            8 : void
            9 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::SwitchDoesNotCoverVariant { ty: Ty::Nil.into() },
                33..145,
                None,
            )]
        },
    )
}

#[test]
fn switch_optional_default() {
    check(
        r#"
        foo :: () {
            switch inner in ?i64.(42) {
                i64 => {
                    inner;
                },
                _ => {
                    inner;
                },
            }
        }
    "#,
        expect![[r#"
            main::foo : () -> void
            0 : i64
            3 : ?i64
            4 : type
            5 : i64
            6 : void
            7 : ?i64
            8 : void
            9 : void
            10 : void
            11 : () -> void
        "#]],
        |_| [],
    )
}

use super::*;

use expect_test::expect;

#[test]
fn if_mismatch() {
    check(
        r#"
            foo :: (bar: bool) -> bool {
                // this evaluates to `<unknown>`, so the function's return type isn't checked
                if bar {
                    "Hello!"
                } else {
                    100
                }
            }
        "#,
        expect![[r#"
            main::foo : main::foo(bool) -> bool
              9 : main::foo(bool) -> bool
            main::lambda#foo : main::foo(bool) -> bool
              2 : bool
              3 : str
              4 : str
              5 : {uint}
              6 : {uint}
              7 : <unknown>
              8 : <unknown>
              9 : main::foo(bool) -> bool
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IfMismatch {
                    first: Ty::String.into(),
                    second: Ty::UInt(0).into(),
                },
                152..256,
                None,
            )]
        },
    );
}

#[test]
fn missing_else() {
    check(
        r#"
            foo :: (arg: bool) -> str {
                if arg {
                    "hello"
                }
            };
        "#,
        expect![[r#"
            main::foo : main::foo(bool) -> str
              7 : main::foo(bool) -> str
            main::lambda#foo : main::foo(bool) -> str
              2 : bool
              3 : str
              4 : str
              5 : str
              6 : str
              7 : main::foo(bool) -> str
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MissingElse {
                    expected: Ty::String.into(),
                },
                57..111,
                Some((
                    TyDiagnosticHelpKind::IfReturnsTypeHere {
                        found: Ty::String.into(),
                    },
                    86..93,
                )),
            )]
        },
    );
}

#[test]
fn if_mismatch_only_return_one() {
    // todo: make the ranges a bit clearer
    check(
        r#"
            foo :: () {
                if true {
                    42
                } else if true {
                    42
                } else if true {
                    "hello"
                } else if true {
                    "hello"
                } else if true {
                    "hello"
                } else if true {
                    42
                } else {
                    42
                };
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              27 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : bool
              1 : {uint}
              2 : {uint}
              3 : bool
              4 : {uint}
              5 : {uint}
              6 : bool
              7 : str
              8 : str
              9 : bool
              10 : str
              11 : str
              12 : bool
              13 : str
              14 : str
              15 : bool
              16 : {uint}
              17 : {uint}
              18 : {uint}
              19 : {uint}
              20 : {uint}
              21 : <unknown>
              22 : <unknown>
              23 : <unknown>
              24 : <unknown>
              25 : <unknown>
              26 : void
              27 : main::foo() -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::IfMismatch {
                    first: Ty::String.into(),
                    second: Ty::UInt(0).into(),
                },
                275..434,
                None,
            )]
        },
    )
}

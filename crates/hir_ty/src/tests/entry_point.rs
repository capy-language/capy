use super::*;

use expect_test::expect;

#[test]
fn entry_point_void() {
    check_impl(
        r#"
            start :: () {};
        "#,
        expect![[r#"
            main::start : main::start() -> void
              1 : main::start() -> void
            main::lambda#start : main::start() -> void
              0 : void
              1 : main::start() -> void
        "#]],
        |_| [],
        Some("start"),
    )
}

#[test]
fn entry_point_int() {
    check_impl(
        r#"
            entry :: () -> i16 { 0 };
        "#,
        expect![[r#"
            main::entry : main::entry() -> i16
              3 : main::entry() -> i16
            main::lambda#entry : main::entry() -> i16
              1 : i16
              2 : i16
              3 : main::entry() -> i16
        "#]],
        |_| [],
        Some("entry"),
    )
}

#[test]
fn entry_point_uint() {
    check_impl(
        r#"
            main :: () -> usize { 0 };
        "#,
        expect![[r#"
            main::main : main::main() -> usize
              3 : main::main() -> usize
            main::lambda#main : main::main() -> usize
              1 : usize
              2 : usize
              3 : main::main() -> usize
        "#]],
        |_| [],
        Some("main"),
    )
}

#[test]
fn entry_point_non_function() {
    check_impl(
        r#"
            main :: 5;
        "#,
        expect![[r#"
            main::main : i32
            0 : i32
        "#]],
        |_| [(TyDiagnosticKind::EntryNotFunction, 13..23, None)],
        Some("main"),
    )
}

#[test]
fn entry_point_bad_params_and_return() {
    check_impl(
        r#"
            foo :: (x: i32, y: bool) -> str {
                "Hello!"
            }
        "#,
        expect![[r#"
            main::foo : main::foo(i32, bool) -> str
              5 : main::foo(i32, bool) -> str
            main::lambda#foo : main::foo(i32, bool) -> str
              3 : str
              4 : str
              5 : main::foo(i32, bool) -> str
        "#]],
        |_| {
            [
                (TyDiagnosticKind::EntryHasParams, 20..37, None),
                (TyDiagnosticKind::EntryBadReturn, 41..44, None),
            ]
        },
        Some("foo"),
    )
}

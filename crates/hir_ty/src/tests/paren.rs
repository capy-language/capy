use super::*;

use expect_test::expect;

#[test]
fn paren_infer() {
    check(
        r#"
            foo :: () -> u16 {
                (42 * (11 / 2))
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> u16
              9 : main::foo() -> u16
            main::lambda#foo : main::foo() -> u16
              1 : u16
              2 : u16
              3 : u16
              4 : u16
              5 : u16
              6 : u16
              7 : u16
              8 : u16
              9 : main::foo() -> u16
        "#]],
        |_| [],
    )
}

#[test]
fn paren_spread() {
    check(
        r#"
            foo :: () {
                x : i8 = 42;
                (42 * ((2 >> x) / 2));
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              13 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : i8
              2 : i8
              3 : i8
              4 : i8
              5 : i8
              6 : i8
              7 : i8
              8 : i8
              9 : i8
              10 : i8
              11 : i8
              12 : void
              13 : main::foo() -> void
              l0 : i8
        "#]],
        |_| [],
    )
}

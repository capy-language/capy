use super::*;

use expect_test::expect;

#[test]
fn defer() {
    check(
        r#"
            foo :: () {
                defer 5 + 5;
                defer foo();
                defer {
                    defer !true;
                };
                defer `blk: {
                    break "owo";
                };
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              11 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : {uint}
              3 : main::foo() -> void
              4 : void
              5 : bool
              6 : bool
              7 : void
              8 : str
              9 : str
              10 : void
              11 : main::foo() -> void
        "#]],
        |_| [],
    )
}

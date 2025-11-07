use super::*;

use expect_test::expect;

mod builtin;
mod is_variant;
mod unwrap;

#[test]
fn unknown_compiler_directive() {
    // todo: the range should include the hash
    check(
        r#"
            Web_Event :: enum {
                Page_Load,
                Page_Unload,
                Key_Press: char,
                Paste: str,
                Click: struct {
                    x: i64,
                    y: i64,
                },
            };

            foo :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                unwrapped := #foo(clicked, Web_Event.Click, 42, bool);
            }
        "#,
        expect![[r#"
            main::Web_Event : type
              5 : type
            main::foo : main::foo() -> void
              19 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              7 : type
              9 : i64
              10 : i64
              11 : main::Web_Event.Click
              12 : main::Web_Event
              13 : type
              14 : type
              15 : {uint}
              16 : type
              17 : <unknown>
              18 : void
              19 : main::foo() -> void
              l0 : main::Web_Event
              l1 : <unknown>
        "#]],
        |i| {
            [(
                TyDiagnosticKind::UnknownDirective {
                    name: i.intern("foo"),
                },
                458..461,
                None,
            )]
        },
    )
}

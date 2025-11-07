use super::*;

use expect_test::expect;

#[test]
fn comptime() {
    check(
        r#"
            foo :: () {
                foo : str = comptime {
                    2 * 5
                };
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              7 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : {uint}
              2 : {uint}
              3 : {uint}
              4 : {uint}
              5 : {uint}
              6 : void
              7 : main::foo() -> void
              l0 : str
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Intern::new(Ty::String)),
                    found: Intern::new(Ty::UInt(0)),
                },
                53..107,
                None,
            )]
        },
    );
}

#[test]
fn comptime_pointer() {
    check(
        r#"
            foo :: () {
                comptime {
                    x := 5;

                    ^x
                };
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              6 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : {uint}
              1 : {uint}
              2 : ^{uint}
              3 : ^{uint}
              4 : <unknown>
              5 : void
              6 : main::foo() -> void
              l0 : {uint}
        "#]],
        |_| [(TyDiagnosticKind::ComptimePointer, 41..121, None)],
    );
}

#[test]
fn comptime_types() {
    check(
        r#"
            Foo :: comptime {
                Bar :: comptime str;
                Baz :: comptime i32;

                struct {
                    a: Bar,
                    b : Baz,
                }
            };

            run :: () {
                my_foo := Foo.{
                    a = "hello",
                    b = 42,
                };
            };
        "#,
        expect![[r#"
            main::Foo : type
              0 : type
              1 : type
              2 : type
              3 : type
              6 : type
              7 : type
              8 : type
              l0 : type
              l1 : type
            main::run : main::run() -> void
              14 : main::run() -> void
            main::lambda#run : main::run() -> void
              10 : str
              11 : i32
              12 : main::Foo
              13 : void
              14 : main::run() -> void
              l2 : main::Foo
        "#]],
        |_| [],
    )
}

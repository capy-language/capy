use super::*;

use expect_test::expect;

#[test]
fn empty_file() {
    check(
        "",
        expect![[r#"
"#]],
        |_| [],
    )
}

#[test]
fn alias_ty_in_other_file() {
    check(
        r#"
            #- main.capy
            foo :: #import("foo.capy");

            Foo :: foo.Foo;

            fun :: () -> Foo {
                foo : Foo = 0;

                foo
            }
            #- foo.capy
            Foo :: distinct i32;
        "#,
        expect![[r#"
            foo::Foo : type
              1 : type
            main::Foo : type
              1 : file foo
              2 : type
            main::foo : file foo
              0 : file foo
            main::fun : main::fun() -> foo::Foo
              8 : main::fun() -> foo::Foo
            main::lambda#fun : main::fun() -> foo::Foo
              5 : foo::Foo
              6 : foo::Foo
              7 : foo::Foo
              8 : main::fun() -> foo::Foo
              l0 : foo::Foo
        "#]],
        |_| [],
    );
}

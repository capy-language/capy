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
            main::Foo : type
            main::foo : file foo
            main::fun : () -> foo::Foo
            foo:
              1 : type
            main:
              0 : file foo
              1 : file foo
              2 : type
              5 : foo::Foo
              6 : foo::Foo
              7 : foo::Foo
              8 : () -> foo::Foo
              l0 : foo::Foo
        "#]],
        |_| [],
    );
}

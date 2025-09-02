use super::*;

use expect_test::expect;

#[test]
fn global() {
    check(
        r#"
        foo :: 2;
    "#,
        expect![[r#"
        main::foo : i32
        0 : i32
    "#]],
        |_| [],
    );
}

#[test]
fn global_and_usage() {
    check(
        r#"
        foo :: 2;

        bar :: () {
            foo;
        };
    "#,
        expect![[r#"
        main::bar : () -> void
        main::foo : i32
        0 : i32
        1 : i32
        2 : void
        3 : () -> void
    "#]],
        |_| [],
    );
}

#[test]
fn non_const_global() {
    check(
        r#"
            foo :: 2 + 2;
        "#,
        expect![[r#"
            main::foo : i32
            0 : i32
            1 : i32
            2 : i32
        "#]],
        |_| [(TyDiagnosticKind::GlobalNotConst, 20..25, None)],
    );
}

#[test]
fn ty_in_other_file() {
    check(
        r#"
            #- main.capy
            numbers :: #import("numbers.capy");

            fun :: () -> numbers.imaginary {
                foo : numbers.imaginary = 0;

                my_magic := numbers.Magic_Struct.{
                    mystical_field = numbers.imaginary.(123),
                };

                my_magic.mystical_field
            }
            #- numbers.capy
            imaginary :: distinct i32;

            Magic_Struct :: struct {
                mystical_field: imaginary,
            };
        "#,
        expect![[r#"
            main::fun : () -> numbers::imaginary
            main::numbers : file numbers
            numbers::Magic_Struct : type
            numbers::imaginary : type
            numbers:
              1 : type
              3 : type
            main:
              0 : file numbers
              1 : file numbers
              3 : file numbers
              5 : numbers::imaginary
              6 : file numbers
              8 : numbers::imaginary
              9 : file numbers
              11 : numbers::imaginary
              12 : numbers::Magic_Struct
              13 : numbers::Magic_Struct
              14 : numbers::imaginary
              15 : numbers::imaginary
              16 : () -> numbers::imaginary
              l0 : numbers::imaginary
              l1 : numbers::Magic_Struct
        "#]],
        |_| [],
    );
}

#[test]
fn alias_ty() {
    check(
        r#"
            Foo :: distinct i32;
            Bar :: Foo;

            fun :: () -> Foo {
                x : Bar = 42;

                x
            }
        "#,
        expect![[r#"
            main::Bar : type
            main::Foo : type
            main::fun : () -> main::Foo
            1 : type
            2 : type
            5 : main::Foo
            6 : main::Foo
            7 : main::Foo
            8 : () -> main::Foo
            l0 : main::Foo
        "#]],
        |_| [],
    );
}

#[test]
fn non_existent_global_in_other_file() {
    check(
        r#"
            #- main.capy
            foo :: #import("foo.capy");
            bar :: foo.bar;

            fun :: () {
                x : bar = 0;
            }
            #- foo.capy
            // nothing here
        "#,
        expect![[r#"
            main::bar : <unknown>
            main::foo : file foo
            main::fun : () -> void
            foo:
            main:
              0 : file foo
              1 : file foo
              2 : <unknown>
              4 : {uint}
              5 : void
              6 : () -> void
              l0 : <unknown>
        "#]],
        |i| {
            [(
                TyDiagnosticKind::UnknownFqn {
                    fqn: hir::Fqn {
                        file: hir::FileName(i.intern("foo.capy")),
                        name: hir::Name(i.intern("bar")),
                    },
                },
                59..66,
                None,
            )]
        },
    );
}

#[test]
fn depend_depend_depend() {
    // while this may seem dumb, it was a bug when first changing hir_ty to be iterative.
    check(
        r#"
            foo :: 5;

            bar :: comptime foo;

            baz :: comptime bar;

            qux :: comptime baz;

            quux :: comptime qux;

            corge :: comptime quux;

            grault :: comptime corge;

            garply :: comptime grault;

            waldo :: comptime garply;

            fred :: comptime waldo;

            plugh :: comptime fred;

            xyzzy :: comptime plugh;

            thud :: comptime xyzzy;
        "#,
        expect![[r#"
            main::bar : i32
            main::baz : i32
            main::corge : i32
            main::foo : i32
            main::fred : i32
            main::garply : i32
            main::grault : i32
            main::plugh : i32
            main::quux : i32
            main::qux : i32
            main::thud : i32
            main::waldo : i32
            main::xyzzy : i32
            0 : i32
            1 : i32
            2 : i32
            3 : i32
            4 : i32
            5 : i32
            6 : i32
            7 : i32
            8 : i32
            9 : i32
            10 : i32
            11 : i32
            12 : i32
            13 : i32
            14 : i32
            15 : i32
            16 : i32
            17 : i32
            18 : i32
            19 : i32
            20 : i32
            21 : i32
            22 : i32
            23 : i32
            24 : i32
        "#]],
        |_| [],
    );
}

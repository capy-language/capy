use super::*;

use expect_test::expect;

#[test]
fn recursive_definitions() {
    check(
        r#"
            foo :: comptime bar;

            bar :: comptime foo;
        "#,
        expect![[r#"
            main::foo : <unknown>
              0 : <unknown>
              1 : <unknown>
            main::bar : <unknown>
              2 : <unknown>
              3 : <unknown>
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("bar")),
                    },
                },
                29..32,
                None,
            )]
        },
    );
}

#[test]
fn recursive_definitions_ty() {
    // the reason these tests were changed:
    //    tests::get_const_on_cyclic_globals
    //    tests::recursive_definitions
    //    tests::recursive_definitions_ty
    // is because `topo` now uses rustc-hash = "2.1"
    // and this changed the order in which things are evaluated.
    // possibly topo should use something order-preserving instead of
    // rustc-hash
    check(
        r#"
            foo : i32 : comptime bar;

            bar : i32 : comptime foo;
        "#,
        expect![[r#"
            main::foo : i32
              1 : <unknown>
              2 : <unknown>
            main::bar : i32
              4 : i32
              5 : i32
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("bar")),
                    },
                },
                34..37,
                None,
            )]
        },
    );
}

#[test]
fn recursive_param_ty() {
    check(
        r#"
            foo :: (bar: foo) {};
        "#,
        expect![[r#"
            main::foo : main::foo(<unknown>) -> void
              2 : main::foo(<unknown>) -> void
            main::lambda#foo : main::foo(<unknown>) -> void
              1 : void
              2 : main::foo(<unknown>) -> void
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("foo")),
                    },
                },
                26..29,
                None,
            )]
        },
    );
}

#[test]
fn recursive_global_ty_annotation() {
    check(
        r#"
            foo : foo : 5;
        "#,
        expect![[r#"
            main::foo : <unknown>
            1 : {uint}
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("foo")),
                    },
                },
                19..22,
                None,
            )]
        },
    );
}

#[test]
fn recursive_local_ty_annotation() {
    // this is handled in hir lowering
    check(
        r#"
            foo :: () {
                a : a = 5;
            };
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              3 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              1 : {uint}
              2 : void
              3 : main::foo() -> void
              l0 : <unknown>
        "#]],
        |_| [],
    );
}

#[test]
fn recursive_struct() {
    // this is handled in hir lowering
    check(
        r#"
            Foo :: struct {
                bar: Foo,
            };
        "#,
        expect![[r#"
            main::Foo : type
            1 : type
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("Foo")),
                    },
                },
                50..53,
                None,
            )]
        },
    );
}

#[test]
fn recursive_struct_and_multiple_literals() {
    // this is handled in hir lowering
    check(
        r#"
            Foo :: struct {
                bar: Foo,
            };

            global_foo :: comptime {
                Foo.{ bar = 0 }
            };

            main :: () {
                my_foo := Foo.{
                    bar = true,
                };
            }
        "#,
        expect![[r#"
            main::Foo : type
              1 : type
            main::global_foo : main::Foo
              3 : {uint}
              4 : main::Foo
              5 : main::Foo
              6 : main::Foo
            main::main : main::main() -> void
              11 : main::main() -> void
            main::lambda#main : main::main() -> void
              8 : bool
              9 : main::Foo
              10 : void
              11 : main::main() -> void
              l0 : main::Foo
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("Foo")),
                    },
                },
                50..53,
                None,
            )]
        },
    );
}

#[test]
fn recursive_distinct() {
    // this is handled in hir lowering
    check(
        r#"
            Foo :: distinct Foo;
        "#,
        expect![[r#"
            main::Foo : type
            1 : type
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("Foo")),
                    },
                },
                29..32,
                None,
            )]
        },
    );
}

#[test]
fn recursive_distinct_and_multiple_instances() {
    // this is handled in hir lowering
    check(
        r#"
            Foo :: distinct Foo;

            global_foo : Foo : comptime {
                0
            };

            main :: () {
                my_foo : Foo = 0;
            }
        "#,
        expect![[r#"
            main::Foo : type
              1 : type
            main::global_foo : main::Foo
              3 : {uint}
              4 : {uint}
              5 : {uint}
            main::main : main::main() -> void
              9 : main::main() -> void
            main::lambda#main : main::main() -> void
              7 : {uint}
              8 : void
              9 : main::main() -> void
              l0 : main::Foo
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("Foo")),
                    },
                },
                29..32,
                None,
            )]
        },
    );
}

#[test]
fn recursive_array() {
    check(
        r#"
            a :: [0] a;
            b : a : 0;
        "#,
        expect![[r#"
            main::a : type
              0 : usize
              2 : type
            main::b : [0]<unknown>
              4 : {uint}
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("a")),
                    },
                },
                22..23,
                None,
            )]
        },
    );
}

#[test]
fn get_const_on_cyclic_globals() {
    // check for https://github.com/capy-language/capy/issues/32

    // todo: if a is inferred before b, then you will get two GlobalNotConst errors
    // but if b is inferred before a, then you will get one GlobalNotConst errors
    //
    // I personally like the second result more, but the errors should be consistent no matter
    // which way it happens.
    //
    // Also there was a weird thing where while testing the example code here I would get a
    // before b, but then while doing `cargo run -- run examples/test.capy` with the example
    // code i would get b before a. I was only able to fix this by changing FxHashMap/Set in
    // the `topo` crate to an IndexMap/Set
    check(
        r#"
            foo :: 1;
            ptr :: 2;
            idx :: 5;
            b   :: a;
            old_gandalf :: struct {};
            b.a = b.a + 1;
        "#,
        expect![[r#"
            main::foo : i32
              0 : i32
            main::ptr : i32
              1 : i32
            main::idx : i32
              2 : i32
            main::b : <unknown>
              3 : <unknown>
            main::old_gandalf : type
              4 : type
            main::a : i32
              5 : <unknown>
              6 : <unknown>
              7 : i32
              8 : i32
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::NotYetResolved {
                        fqn: Fqn {
                            file: FileName(i.intern("main.capy")),
                            name: Name(i.intern("a")),
                        },
                    },
                    86..87,
                    None,
                ),
                (TyDiagnosticKind::GlobalNotConst, 145..152, None),
            ]
        },
    )
}

#[test]
fn recursive_global() {
    // check for https://github.com/capy-language/capy/issues/30
    check(
        r#"
            a :: a;
        "#,
        expect![[r#"
            main::a : <unknown>
            0 : <unknown>
        "#]],
        |i| {
            [(
                TyDiagnosticKind::NotYetResolved {
                    fqn: Fqn {
                        file: FileName(i.intern("main.capy")),
                        name: Name(i.intern("a")),
                    },
                },
                18..19,
                None,
            )]
        },
    )
}

#[test]
fn recursive_function_defined_first() {
    check(
        r#"
            foo :: () { foo() }

            main :: () {
                foo();
            }
        "#,
        expect![[r#"
            main::foo : main::foo() -> void
              3 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : main::foo() -> void
              1 : void
              2 : void
              3 : main::foo() -> void
            main::main : main::main() -> void
              7 : main::main() -> void
            main::lambda#main : main::main() -> void
              4 : main::foo() -> void
              5 : void
              6 : void
              7 : main::main() -> void
        "#]],
        |_| [],
    );
}

#[test]
fn recursive_function_defined_second() {
    // when cyclic definitions are sorted, if they're sorted incorrectly,
    // this input will produce incorrect cyclic errors

    // NOTE: if the sorted was wrong `recursive_function_defined_first` would
    // fail ONLY if you put the input in a file and ran the file.
    // This is because "main" (the name of the entry point) will be interned early,
    // causing "main" to be sorted first and "foo" to be sorted second.
    check(
        r#"
            main :: () {
                foo();
            }

            foo :: () { foo() }
        "#,
        expect![[r#"
            main::main : main::main() -> void
              3 : main::main() -> void
            main::lambda#main : main::main() -> void
              0 : main::foo() -> void
              1 : void
              2 : void
              3 : main::main() -> void
            main::foo : main::foo() -> void
              7 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              4 : main::foo() -> void
              5 : void
              6 : void
              7 : main::foo() -> void
        "#]],
        |_| [],
    );
}

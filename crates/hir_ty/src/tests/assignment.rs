use super::*;

use expect_test::expect;

#[test]
fn assign_var() {
    check(
        r#"
            main :: () {
                foo := 5;

                foo = 42;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : void
            4 : () -> void
            l0 : {uint}
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_binding() {
    check(
        r#"
            main :: () {
                foo :: 5;

                foo = 42;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : void
            4 : () -> void
            l0 : {uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                69..78,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 42..51)),
            )]
        },
    );
}

#[test]
fn assign_to_immutable_ref() {
    check(
        r#"
            main :: () {
                foo := 5;
                bar :: ^foo; 

                bar^ = 42;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^{uint}
            3 : ^{uint}
            4 : {uint}
            5 : {uint}
            6 : void
            7 : () -> void
            l0 : {uint}
            l1 : ^{uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                99..109,
                Some((TyDiagnosticHelpKind::ImmutableRef, 75..79)),
            )]
        },
    );
}

#[test]
fn assign_to_mut_ref() {
    check(
        r#"
            main :: () {
                foo := 5;
                bar :: ^mut foo; 

                bar^ = 42;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^mut {uint}
            3 : ^mut {uint}
            4 : {uint}
            5 : {uint}
            6 : void
            7 : () -> void
            l0 : {uint}
            l1 : ^mut {uint}
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_binary_expr() {
    check(
        r#"
            main :: () {
                2 + 2 = 5;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : {uint}
            2 : {uint}
            3 : {uint}
            4 : void
            5 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                42..52,
                Some((TyDiagnosticHelpKind::CannotMutateExpr, 42..47)),
            )]
        },
    );
}

#[test]
fn assign_to_mut_struct_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            foo :: () {
                bob := Person.{
                    name = "Bob",
                    age = 26,
                };

                bob.age = bob.age + 1;
            }
        "#,
        expect![[r#"
            main::Person : type
            main::foo : () -> void
            2 : type
            4 : str
            5 : i32
            6 : main::Person
            7 : main::Person
            8 : i32
            9 : main::Person
            10 : i32
            11 : i32
            12 : i32
            13 : void
            14 : () -> void
            l0 : main::Person
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_immutable_struct_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            foo :: () {
                bob :: Person.{
                    name = "Bob",
                    age = 26,
                };

                bob.age = bob.age + 1;
            }
        "#,
        expect![[r#"
            main::Person : type
            main::foo : () -> void
            2 : type
            4 : str
            5 : i32
            6 : main::Person
            7 : main::Person
            8 : i32
            9 : main::Person
            10 : i32
            11 : i32
            12 : i32
            13 : void
            14 : () -> void
            l0 : main::Person
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                256..278,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 140..238)),
            )]
        },
    );
}

#[test]
fn assign_to_mut_struct_array_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            Company :: struct {
                employees: [3]Person,
            };

            foo :: () {
                my_company := Company.{
                    employees = Person.[
                        Person.{
                            name = "Bob",
                            age = 26,
                        },
                        Person.{
                            name = "Kyle",
                            age = 30,
                        },
                        Person.{
                            name = "John",
                            age = 23,
                        }
                    ],
                };

                my_company.employees[1].age = my_company.employees[1].age + 1;
            }
        "#,
        expect![[r#"
            main::Company : type
            main::Person : type
            main::foo : () -> void
            2 : type
            3 : usize
            6 : type
            10 : str
            11 : i32
            12 : main::Person
            14 : str
            15 : i32
            16 : main::Person
            18 : str
            19 : i32
            20 : main::Person
            21 : [3]main::Person
            22 : main::Company
            23 : main::Company
            24 : [3]main::Person
            25 : usize
            26 : main::Person
            27 : i32
            28 : main::Company
            29 : [3]main::Person
            30 : usize
            31 : main::Person
            32 : i32
            33 : i32
            34 : i32
            35 : void
            36 : () -> void
            l0 : main::Company
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_immutable_struct_array_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            Company :: struct {
                employees: [3]Person,
            };

            foo :: () {
                my_company :: Company.{
                    employees = Person.[
                        Person.{
                            name = "Bob",
                            age = 26,
                        },
                        Person.{
                            name = "Kyle",
                            age = 30,
                        },
                        Person.{
                            name = "John",
                            age = 23,
                        }
                    ],
                };

                my_company.employees[1].age = my_company.employees[1].age + 1;
            }
        "#,
        expect![[r#"
            main::Company : type
            main::Person : type
            main::foo : () -> void
            2 : type
            3 : usize
            6 : type
            10 : str
            11 : i32
            12 : main::Person
            14 : str
            15 : i32
            16 : main::Person
            18 : str
            19 : i32
            20 : main::Person
            21 : [3]main::Person
            22 : main::Company
            23 : main::Company
            24 : [3]main::Person
            25 : usize
            26 : main::Person
            27 : i32
            28 : main::Company
            29 : [3]main::Person
            30 : usize
            31 : main::Person
            32 : i32
            33 : i32
            34 : i32
            35 : void
            36 : () -> void
            l0 : main::Company
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                771..833,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 226..753)),
            )]
        },
    );
}

// todo: do a separate test to make sure the compile handles `^Person.{}` vs `^(Person.{})`
#[test]
fn assign_to_struct_immutable_ref_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            Ref_To_Person :: struct {
                person: ^Person,
            };

            foo :: () {
                ref :: Ref_To_Person.{
                    person = ^(Person.{
                        name = "Bob",
                        age = 26,
                    }),
                };

                ref.person^.age = ref.person^.age + 1;
            }
        "#,
        expect![[r#"
            main::Person : type
            main::Ref_To_Person : type
            main::foo : () -> void
            2 : type
            5 : type
            8 : str
            9 : i32
            10 : main::Person
            11 : main::Person
            12 : ^main::Person
            13 : main::Ref_To_Person
            14 : main::Ref_To_Person
            15 : ^main::Person
            16 : main::Person
            17 : i32
            18 : main::Ref_To_Person
            19 : ^main::Person
            20 : main::Person
            21 : i32
            22 : i32
            23 : i32
            24 : void
            25 : () -> void
            l0 : main::Ref_To_Person
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                422..460,
                Some((TyDiagnosticHelpKind::ImmutableRef, 426..432)),
            )]
        },
    );
}

// todo: do a test with the old way this was "^mut (Person.{})" vs "^mut Person.{}"
#[test]
fn assign_to_struct_mut_ref_field() {
    check(
        r#"
            Person :: struct {
                name: str,
                age: i32
            };

            Ref_To_Person :: struct {
                person: ^mut Person,
            };

            foo :: () {
                ref :: Ref_To_Person.{
                    person = ^mut (Person.{
                        name = "Bob",
                        age = 26,
                    }),
                };

                ref.person^.age = ref.person^.age + 1;
            }
        "#,
        expect![[r#"
            main::Person : type
            main::Ref_To_Person : type
            main::foo : () -> void
            2 : type
            5 : type
            8 : str
            9 : i32
            10 : main::Person
            11 : main::Person
            12 : ^mut main::Person
            13 : main::Ref_To_Person
            14 : main::Ref_To_Person
            15 : ^mut main::Person
            16 : main::Person
            17 : i32
            18 : main::Ref_To_Person
            19 : ^mut main::Person
            20 : main::Person
            21 : i32
            22 : i32
            23 : i32
            24 : void
            25 : () -> void
            l0 : main::Ref_To_Person
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_mut_array() {
    check(
        r#"
            foo :: () {
                array := i32.[1, 2, 3];

                array[0] = 100;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : usize
            7 : i32
            8 : i32
            9 : void
            10 : () -> void
            l0 : [3]i32
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_immutable_array() {
    check(
        r#"
            foo :: () {
                array :: i32.[1, 2, 3];

                array[0] = 100;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            1 : i32
            2 : i32
            3 : i32
            4 : [3]i32
            5 : [3]i32
            6 : usize
            7 : i32
            8 : {uint}
            9 : void
            10 : () -> void
            l0 : [3]i32
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                82..97,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 41..64)),
            )]
        },
    );
}

#[test]
fn assign_to_param() {
    check(
        r#"
            foo :: (x: i32) {
                x = 5;
            }
        "#,
        expect![[r#"
            main::foo : (i32) -> void
            1 : i32
            2 : {uint}
            3 : void
            4 : (i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                47..53,
                Some((
                    TyDiagnosticHelpKind::ImmutableParam { assignment: true },
                    21..27,
                )),
            )]
        },
    );
}

#[test]
fn assign_to_param_array() {
    check(
        r#"
            foo :: (array: [3]i32) {
                array[0] = 5;
            }
        "#,
        expect![[r#"
            main::foo : ([3]i32) -> void
            0 : usize
            3 : [3]i32
            4 : usize
            5 : i32
            6 : {uint}
            7 : void
            8 : ([3]i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                54..67,
                Some((
                    TyDiagnosticHelpKind::ImmutableParam { assignment: true },
                    21..34,
                )),
            )]
        },
    );
}

#[test]
fn assign_to_param_immutable_ref() {
    check(
        r#"
            foo :: (bruh: ^i32) {
                bruh^ = 5;
            }
        "#,
        expect![[r#"
            main::foo : (^i32) -> void
            2 : ^i32
            3 : i32
            4 : {uint}
            5 : void
            6 : (^i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                51..61,
                Some((TyDiagnosticHelpKind::ImmutableRef, 21..31)),
            )]
        },
    );
}

#[test]
fn assign_to_param_mut_ref() {
    check(
        r#"
            foo :: (array: ^mut i32) {
                array^ = 5;
            }
        "#,
        expect![[r#"
            main::foo : (^mut i32) -> void
            2 : ^mut i32
            3 : i32
            4 : i32
            5 : void
            6 : (^mut i32) -> void
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_param_immutable_ref_no_deref() {
    // todo: I think this should show a recommendation to use `^=` first before suggesting that you
    // use `^mut`
    check(
        r#"
            foo :: (bruh: ^i32) {
                bruh = 5;
            }
        "#,
        expect![[r#"
            main::foo : (^i32) -> void
            2 : ^i32
            3 : {uint}
            4 : void
            5 : (^i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                51..60,
                Some((TyDiagnosticHelpKind::ImmutableRef, 21..31)),
            )]
        },
    );
}

#[test]
fn assign_to_param_mut_ref_no_deref() {
    check(
        r#"
            foo :: (bruh: ^mut i32) {
                bruh = 5;
            }
        "#,
        expect![[r#"
            main::foo : (^mut i32) -> void
            2 : ^mut i32
            3 : {uint}
            4 : void
            5 : (^mut i32) -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                55..64,
                Some((TyDiagnosticHelpKind::NotMutatingRefThroughDeref, 55..59)),
            )]
        },
    );
}

#[test]
fn assign_to_global() {
    check(
        r#"
            foo :: 5;

            bar :: () {
                foo = 5;
            }
        "#,
        expect![[r#"
            main::bar : () -> void
            main::foo : i32
            0 : i32
            1 : i32
            2 : {uint}
            3 : void
            4 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                64..72,
                Some((TyDiagnosticHelpKind::ImmutableGlobal, 13..22)),
            )]
        },
    );
}

#[test]
fn assign_to_global_in_other_file() {
    // todo: this should show the declaration of the global in the other file
    check(
        r#"
            #- main.capy
            other_file :: #import("other_file.capy");

            func :: () {
                other_file.foo = 25;
            }
            #- other_file.capy
            foo :: 5;
        "#,
        expect![[r#"
            main::func : () -> void
            main::other_file : file other_file
            other_file::foo : i32
            other_file:
              0 : i32
            main:
              0 : file other_file
              1 : file other_file
              2 : i32
              3 : {uint}
              4 : void
              5 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                96..116,
                Some((TyDiagnosticHelpKind::ImmutableGlobal, 107..110)),
            )]
        },
    );
}

#[test]
fn assign_to_immutable_ref_binding_no_deref() {
    check(
        r#"
            foo :: () {
                bar :: 5;

                baz :: ^bar;

                baz = 25;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^{uint}
            3 : ^{uint}
            4 : {uint}
            5 : void
            6 : () -> void
            l0 : {uint}
            l1 : ^{uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                98..107,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 68..80)),
            )]
        },
    );
}

#[test]
fn assign_to_mut_ref_binding_no_deref() {
    // todo: this should recommend using `^=` instead of recommending changing the variable to `:=`
    check(
        r#"
            foo :: () {
                bar := 5;

                baz :: ^mut bar;

                baz = 25;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^mut {uint}
            3 : ^mut {uint}
            4 : {uint}
            5 : void
            6 : () -> void
            l0 : {uint}
            l1 : ^mut {uint}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::CannotMutate,
                102..111,
                Some((TyDiagnosticHelpKind::ImmutableBinding, 68..84)),
            )]
        },
    );
}

#[test]
fn assign_to_immutable_ref_variable_no_deref() {
    check(
        r#"
            foo :: () {
                val_a :: 5;
                ptr_a := ^val_a;

                val_b :: 42;
                ptr_b :: ^val_b;

                ptr_a = ptr_b;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^{uint}
            3 : {uint}
            4 : {uint}
            5 : ^{uint}
            6 : ^{uint}
            7 : ^{uint}
            8 : void
            9 : () -> void
            l0 : {uint}
            l1 : ^{uint}
            l2 : {uint}
            l3 : ^{uint}
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_mut_ref_varibale_no_deref() {
    check(
        r#"
            foo :: () {
                val_a := 5;
                ptr_a := ^mut val_a;

                val_b := 42;
                ptr_b :: ^mut val_b;

                ptr_a = ptr_b;
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : {uint}
            2 : ^mut {uint}
            3 : {uint}
            4 : {uint}
            5 : ^mut {uint}
            6 : ^mut {uint}
            7 : ^mut {uint}
            8 : void
            9 : () -> void
            l0 : {uint}
            l1 : ^mut {uint}
            l2 : {uint}
            l3 : ^mut {uint}
        "#]],
        |_| [],
    );
}

#[test]
fn assign_to_mut_ref_expr() {
    check(
        r#"
            main :: () {
                {^mut 2}^ = 5;
            };
        "#,
        expect![[r#"
            main::main : () -> void
            0 : {uint}
            1 : ^mut {uint}
            2 : ^mut {uint}
            3 : {uint}
            4 : {uint}
            5 : void
            6 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::MutableRefToImmutableData,
                43..49,
                Some((TyDiagnosticHelpKind::CannotMutateExpr, 48..49)),
            )]
        },
    );
}

use super::*;

use expect_test::expect;

#[test]
fn empty_enum() {
    check(
        r#"
            My_Awesome_Enum :: enum {
                Foo,
                Bar
            };

            main :: () {
                my_foo : My_Awesome_Enum.Foo = My_Awesome_Enum.Foo.(());
                my_bar : My_Awesome_Enum.Bar = My_Awesome_Enum.Bar.(());
            }
        "#,
        expect![[r#"
            main::My_Awesome_Enum : type
            main::main : () -> void
            0 : type
            1 : type
            3 : void
            4 : type
            6 : main::My_Awesome_Enum.Foo
            7 : type
            9 : void
            10 : type
            12 : main::My_Awesome_Enum.Bar
            13 : void
            14 : () -> void
            l0 : main::My_Awesome_Enum.Foo
            l1 : main::My_Awesome_Enum.Bar
        "#]],
        |_| [],
    )
}

#[test]
fn typed_enum_with_discriminants() {
    check(
        r#"
            My_Awesome_Enum :: enum {
                Foo,
                Bar: i32,
                Baz: str | 42,
                Qux: bool
            };

            main :: () {
                my_foo : My_Awesome_Enum.Foo = My_Awesome_Enum.Foo.(());
                my_bar : My_Awesome_Enum.Bar = My_Awesome_Enum.Bar.(5);
                my_baz : My_Awesome_Enum.Baz = My_Awesome_Enum.Baz.("hello");
                my_qux : My_Awesome_Enum.Qux = My_Awesome_Enum.Qux.(true);
            }
        "#,
        expect![[r#"
            main::My_Awesome_Enum : type
            main::main : () -> void
            2 : u8
            4 : type
            5 : type
            7 : void
            8 : type
            10 : main::My_Awesome_Enum.Foo
            11 : type
            13 : i32
            14 : type
            16 : main::My_Awesome_Enum.Bar
            17 : type
            19 : str
            20 : type
            22 : main::My_Awesome_Enum.Baz
            23 : type
            25 : bool
            26 : type
            28 : main::My_Awesome_Enum.Qux
            29 : void
            30 : () -> void
            l0 : main::My_Awesome_Enum.Foo
            l1 : main::My_Awesome_Enum.Bar
            l2 : main::My_Awesome_Enum.Baz
            l3 : main::My_Awesome_Enum.Qux
        "#]],
        |_| [],
    )
}

#[test]
fn autocast_variant_to_enum_variable() {
    check(
        r#"
            Animal :: enum {
                Dog: str,
                Fish: i32, // maybe this is the fish's age or something
            };

            main :: () {
                my_dog := Animal.Dog.("George");
                my_fish := Animal.Fish.(1000);

                animal_1 : Animal = my_dog;
                animal_2 : Animal = my_fish;
            }
        "#,
        expect![[r#"
            main::Animal : type
            main::main : () -> void
            2 : type
            3 : str
            4 : type
            6 : main::Animal.Dog
            7 : i32
            8 : type
            10 : main::Animal.Fish
            12 : main::Animal.Dog
            14 : main::Animal.Fish
            15 : void
            16 : () -> void
            l0 : main::Animal.Dog
            l1 : main::Animal.Fish
            l2 : main::Animal
            l3 : main::Animal
        "#]],
        |_| [],
    )
}

#[test]
fn autocast_variant_to_enum_function() {
    check(
        r#"
            Animal :: enum {
                Dog: str,
                Fish: i32, // maybe this is the fish's age or something
            };

            main :: () {
                my_dog := Animal.Dog.("George");
                my_fish := Animal.Fish.(1000);

                go_do_animal_stuff_idk(my_dog);
                go_do_animal_stuff_idk(my_fish);
            }

            go_do_animal_stuff_idk :: (animal: Animal) {
                // imagine the craziest code here
            }
        "#,
        expect![[r#"
            main::Animal : type
            main::go_do_animal_stuff_idk : (main::Animal) -> void
            main::main : () -> void
            2 : type
            3 : str
            4 : type
            6 : main::Animal.Dog
            7 : i32
            8 : type
            10 : main::Animal.Fish
            11 : (main::Animal) -> void
            12 : main::Animal.Dog
            13 : void
            14 : (main::Animal) -> void
            15 : main::Animal.Fish
            16 : void
            17 : void
            18 : () -> void
            20 : void
            21 : (main::Animal) -> void
            l0 : main::Animal.Dog
            l1 : main::Animal.Fish
        "#]],
        |_| [],
    )
}

#[test]
fn cast_variant_to_enum_function() {
    check(
        r#"
            Animal :: enum {
                Dog: str,
                Fish: i32, // maybe this is the fish's age or something
            };

            main :: () {
                my_dog := Animal.Dog.("George");
                my_fish := Animal.Fish.(1000);

                go_do_animal_stuff_idk(Animal.(my_dog));
                go_do_animal_stuff_idk(Animal.(my_fish));
            }

            go_do_animal_stuff_idk :: (animal: Animal) {
                // imagine the craziest code here
            }
        "#,
        expect![[r#"
            main::Animal : type
            main::go_do_animal_stuff_idk : (main::Animal) -> void
            main::main : () -> void
            2 : type
            3 : str
            4 : type
            6 : main::Animal.Dog
            7 : i32
            8 : type
            10 : main::Animal.Fish
            11 : (main::Animal) -> void
            12 : main::Animal.Dog
            14 : main::Animal
            15 : void
            16 : (main::Animal) -> void
            17 : main::Animal.Fish
            19 : main::Animal
            20 : void
            21 : void
            22 : () -> void
            24 : void
            25 : (main::Animal) -> void
            l0 : main::Animal.Dog
            l1 : main::Animal.Fish
        "#]],
        |_| [],
    )
}

#[test]
fn switch() {
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

                switch e in clicked {
                    .Page_Load => {
                        e;
                        1; // this is done so that the `e`s are clearly visible below
                    },
                    .Page_Unload => {
                        e;
                        true;
                    },
                    .Key_Press => {
                        e;
                        "";
                    },
                    .Paste => {
                        e;
                        ' ';
                    },
                    .Click => {
                        e;
                        e.x;
                    },
                }
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            12 : main::Web_Event
            13 : main::Web_Event.Page_Load
            14 : {uint}
            15 : void
            16 : main::Web_Event.Page_Unload
            17 : bool
            18 : void
            19 : main::Web_Event.Key_Press
            20 : str
            21 : void
            22 : main::Web_Event.Paste
            23 : char
            24 : void
            25 : main::Web_Event.Click
            26 : main::Web_Event.Click
            27 : i64
            28 : void
            29 : void
            30 : void
            31 : () -> void
            l0 : main::Web_Event
        "#]],
        |_| [],
    )
}

#[test]
fn switch_val() {
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

                val : i16 = switch e in clicked {
                    .Page_Load => {
                        e;
                        10
                    },
                    .Page_Unload => {
                        e;
                        20
                    },
                    .Key_Press => {
                        e;
                        30
                    },
                    .Paste => {
                        e;
                        40
                    },
                    .Click => {
                        e;
                        50
                    }
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : main::Web_Event.Page_Load
            15 : i16
            16 : i16
            17 : main::Web_Event.Page_Unload
            18 : i16
            19 : i16
            20 : main::Web_Event.Key_Press
            21 : i16
            22 : i16
            23 : main::Web_Event.Paste
            24 : i16
            25 : i16
            26 : main::Web_Event.Click
            27 : i16
            28 : i16
            29 : i16
            30 : void
            31 : () -> void
            l0 : main::Web_Event
            l1 : i16
        "#]],
        |_| [],
    )
}

#[test]
fn switch_val_fully_qualified() {
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

                val : i16 = switch e in clicked {
                    Web_Event.Page_Load => {
                        e;
                        10
                    },
                    Web_Event.Page_Unload => {
                        e;
                        20
                    },
                    Web_Event.Key_Press => {
                        e;
                        30
                    },
                    Web_Event.Paste => {
                        e;
                        40
                    },
                    Web_Event.Click => {
                        e;
                        50
                    }
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : type
            15 : main::Web_Event.Page_Load
            16 : main::Web_Event.Page_Load
            17 : i16
            18 : i16
            19 : type
            20 : main::Web_Event.Page_Unload
            21 : main::Web_Event.Page_Unload
            22 : i16
            23 : i16
            24 : type
            25 : type
            26 : main::Web_Event.Key_Press
            27 : i16
            28 : i16
            29 : type
            30 : type
            31 : main::Web_Event.Paste
            32 : i16
            33 : i16
            34 : type
            35 : type
            36 : main::Web_Event.Click
            37 : i16
            38 : i16
            39 : i16
            40 : void
            41 : () -> void
            l0 : main::Web_Event
            l1 : i16
        "#]],
        |_| [],
    )
}

#[test]
fn switch_val_fully_qualified_and_shorthand() {
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

                val : i16 = switch e in clicked {
                    Web_Event.Page_Load => {
                        e;
                        10
                    },
                    Web_Event.Page_Unload => {
                        e;
                        20
                    },
                    .Key_Press => {
                        e;
                        30
                    },
                    Web_Event.Paste => {
                        e;
                        40
                    },
                    .Click => {
                        e;
                        50
                    }
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : type
            15 : main::Web_Event.Page_Load
            16 : main::Web_Event.Page_Load
            17 : i16
            18 : i16
            19 : type
            20 : main::Web_Event.Page_Unload
            21 : main::Web_Event.Page_Unload
            22 : i16
            23 : i16
            24 : main::Web_Event.Key_Press
            25 : i16
            26 : i16
            27 : type
            28 : type
            29 : main::Web_Event.Paste
            30 : i16
            31 : i16
            32 : main::Web_Event.Click
            33 : i16
            34 : i16
            35 : i16
            36 : void
            37 : () -> void
            l0 : main::Web_Event
            l1 : i16
        "#]],
        |_| [],
    )
}

#[test]
fn switch_mismatch_val() {
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

                val : u8 = switch e in clicked {
                    .Page_Load => {
                        e;
                        10
                    },
                    .Page_Unload => {
                        e;
                        20
                    },
                    .Key_Press => {
                        e;
                        "hello"
                    },
                    .Paste => {
                        e;
                        true
                    },
                    .Click => {
                        e;
                        ' '
                    }
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : main::Web_Event.Page_Load
            15 : {uint}
            16 : {uint}
            17 : main::Web_Event.Page_Unload
            18 : {uint}
            19 : {uint}
            20 : main::Web_Event.Key_Press
            21 : str
            22 : str
            23 : main::Web_Event.Paste
            24 : bool
            25 : bool
            26 : main::Web_Event.Click
            27 : char
            28 : char
            29 : <unknown>
            30 : void
            31 : () -> void
            l0 : main::Web_Event
            l1 : u8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::SwitchMismatch {
                    other: Ty::String.into(),
                    first: Ty::UInt(0).into(),
                },
                739..821,
                None,
            )]
        },
    )
}

#[test]
fn switch_missing_variant() {
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

                val : i128 = switch e in clicked {
                    .Page_Load => {
                        e;
                        10
                    },
                    .Page_Unload => {
                        e;
                        20
                    },
                    .Key_Press => {
                        e;
                        "hello"
                    },
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : main::Web_Event.Page_Load
            15 : {uint}
            16 : {uint}
            17 : main::Web_Event.Page_Unload
            18 : {uint}
            19 : {uint}
            20 : main::Web_Event.Key_Press
            21 : str
            22 : str
            23 : <unknown>
            24 : void
            25 : () -> void
            l0 : main::Web_Event
            l1 : i128
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::SwitchMismatch {
                        other: Ty::String.into(),
                        first: Ty::UInt(0).into(),
                    },
                    741..823,
                    None,
                ),
                (
                    TyDiagnosticKind::SwitchDoesNotCoverVariant {
                        ty: Ty::EnumVariant {
                            enum_uid: 6,
                            variant_name: hir::Name(i.intern("Paste")),
                            uid: 3,
                            sub_ty: Ty::String.into(),
                            discriminant: 3,
                        }
                        .into(),
                    },
                    457..842,
                    None,
                ),
                (
                    TyDiagnosticKind::SwitchDoesNotCoverVariant {
                        ty: Ty::EnumVariant {
                            enum_uid: 6,
                            variant_name: hir::Name(i.intern("Click")),
                            uid: 5,
                            sub_ty: Ty::ConcreteStruct {
                                uid: 4,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("x")),
                                        ty: Ty::IInt(64).into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("y")),
                                        ty: Ty::IInt(64).into(),
                                    },
                                ],
                            }
                            .into(),
                            discriminant: 4,
                        }
                        .into(),
                    },
                    457..842,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn switch_duplicate_arms() {
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

                switch e in clicked {
                    .Page_Load => {
                        e;
                        1; // this is done so that the `e`s are clearly visible below
                    },
                    .Page_Unload => {
                        e;
                        true;
                    },
                    .Key_Press => {
                        e;
                        "";
                    },
                    .Paste => {
                        e;
                        ' ';
                    },
                    .Click => {
                        e;
                        e.x;
                    },
                    .Page_Unload => {
                        e;
                        0;
                    }
                }
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            12 : main::Web_Event
            13 : main::Web_Event.Page_Load
            14 : {uint}
            15 : void
            16 : main::Web_Event.Page_Unload
            17 : bool
            18 : void
            19 : main::Web_Event.Key_Press
            20 : str
            21 : void
            22 : main::Web_Event.Paste
            23 : char
            24 : void
            25 : main::Web_Event.Click
            26 : main::Web_Event.Click
            27 : i64
            28 : void
            29 : main::Web_Event.Page_Unload
            30 : {uint}
            31 : void
            32 : void
            33 : void
            34 : () -> void
            l0 : main::Web_Event
        "#]],
        |i| {
            [(
                TyDiagnosticKind::SwitchAlreadyCoversVariant {
                    ty: Ty::EnumVariant {
                        enum_uid: 6,
                        variant_name: hir::Name(i.intern("Page_Unload")),
                        uid: 1,
                        sub_ty: Ty::Void.into(),
                        discriminant: 1,
                    }
                    .into(),
                },
                1112..1124,
                None,
            )]
        },
    )
}

#[test]
fn switch_duplicate_arms_fully_qualified_and_shorthand() {
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

                switch e in clicked {
                    .Page_Load => {
                        e;
                        1; // this is done so that the `e`s are clearly visible below
                    },
                    Web_Event.Page_Unload => {
                        e;
                        true;
                    },
                    .Key_Press => {
                        e;
                        "";
                    },
                    .Page_Unload => {
                        e;
                        0;
                    },
                    .Paste => {
                        e;
                        ' ';
                    },
                    Web_Event.Page_Unload => {
                        e;
                        false;
                    },
                    .Click => {
                        e;
                        e.x;
                    },
                }
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            12 : main::Web_Event
            13 : main::Web_Event.Page_Load
            14 : {uint}
            15 : void
            16 : type
            17 : main::Web_Event.Page_Unload
            18 : main::Web_Event.Page_Unload
            19 : bool
            20 : void
            21 : main::Web_Event.Key_Press
            22 : str
            23 : void
            24 : main::Web_Event.Page_Unload
            25 : {uint}
            26 : void
            27 : main::Web_Event.Paste
            28 : char
            29 : void
            30 : type
            31 : main::Web_Event.Page_Unload
            32 : main::Web_Event.Page_Unload
            33 : bool
            34 : void
            35 : main::Web_Event.Click
            36 : main::Web_Event.Click
            37 : i64
            38 : void
            39 : void
            40 : void
            41 : () -> void
            l0 : main::Web_Event
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::SwitchAlreadyCoversVariant {
                        ty: Ty::EnumVariant {
                            enum_uid: 6,
                            variant_name: hir::Name(i.intern("Page_Unload")),
                            uid: 1,
                            sub_ty: Ty::Void.into(),
                            discriminant: 1,
                        }
                        .into(),
                    },
                    899..911,
                    None,
                ),
                (
                    TyDiagnosticKind::SwitchAlreadyCoversVariant {
                        ty: Ty::EnumVariant {
                            enum_uid: 6,
                            variant_name: hir::Name(i.intern("Page_Unload")),
                            uid: 1,
                            sub_ty: Ty::Void.into(),
                            discriminant: 1,
                        }
                        .into(),
                    },
                    1125..1146,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn switch_default() {
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

                val : u16 = switch e in clicked {
                    .Page_Load => {
                        e;
                        10
                    },
                    .Page_Unload => {
                        e;
                        20
                    },
                    .Key_Press => {
                        e;
                        30
                    },
                    _ => 40,
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : main::Web_Event.Page_Load
            15 : u16
            16 : u16
            17 : main::Web_Event.Page_Unload
            18 : u16
            19 : u16
            20 : main::Web_Event.Key_Press
            21 : u16
            22 : u16
            23 : u16
            24 : u16
            25 : void
            26 : () -> void
            l0 : main::Web_Event
            l1 : u16
        "#]],
        |_| [],
    )
}

#[test]
fn switch_default_fully_qualified() {
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

                val : u16 = switch e in clicked {
                    Web_Event.Page_Load => {
                        e;
                        10
                    },
                    Web_Event.Page_Unload => {
                        e;
                        20
                    },
                    Web_Event.Key_Press => {
                        e;
                        30
                    },
                    _ => 40,
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : type
            15 : main::Web_Event.Page_Load
            16 : main::Web_Event.Page_Load
            17 : u16
            18 : u16
            19 : type
            20 : main::Web_Event.Page_Unload
            21 : main::Web_Event.Page_Unload
            22 : u16
            23 : u16
            24 : type
            25 : type
            26 : main::Web_Event.Key_Press
            27 : u16
            28 : u16
            29 : u16
            30 : u16
            31 : void
            32 : () -> void
            l0 : main::Web_Event
            l1 : u16
        "#]],
        |_| [],
    )
}

#[test]
fn switch_default_mismatch() {
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

                val : u16 = switch e in clicked {
                    .Page_Load => {
                        e;
                        10
                    },
                    .Page_Unload => {
                        e;
                        20
                    },
                    .Key_Press => {
                        e;
                        30
                    },
                    _ => "hello",
                };
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            13 : main::Web_Event
            14 : main::Web_Event.Page_Load
            15 : {uint}
            16 : {uint}
            17 : main::Web_Event.Page_Unload
            18 : {uint}
            19 : {uint}
            20 : main::Web_Event.Key_Press
            21 : {uint}
            22 : {uint}
            23 : str
            24 : <unknown>
            25 : void
            26 : () -> void
            l0 : main::Web_Event
            l1 : u16
        "#]],
        |_| {
            [(
                TyDiagnosticKind::SwitchMismatch {
                    other: Ty::String.into(),
                    first: Ty::UInt(0).into(),
                },
                844..851,
                None,
            )]
        },
    )
}

#[test]
fn switch_not_shorthand() {
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

                switch e in clicked {
                    .Page_Load => {
                        e;
                        1; // this is done so that the `e`s are clearly visible below
                    },
                    .Page_Unload => {
                        e;
                        true;
                    },
                    .Key_Press => {
                        e;
                        "";
                    },
                    .Crazy_Kool_Variant => {
                        e;
                        0.0;
                    },
                    .Paste => {
                        e;
                        ' ';
                    },
                    .Click => {
                        e;
                        e.x;
                    },
                    .Other_Kool_Variant => {
                        e;
                        0.0;
                    },
                }
            }
        "#,
        expect![[r#"
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            7 : type
            9 : i64
            10 : i64
            11 : main::Web_Event.Click
            12 : main::Web_Event
            13 : main::Web_Event.Page_Load
            14 : {uint}
            15 : void
            16 : main::Web_Event.Page_Unload
            17 : bool
            18 : void
            19 : main::Web_Event.Key_Press
            20 : str
            21 : void
            22 : <unknown>
            23 : {float}
            24 : void
            25 : main::Web_Event.Paste
            26 : char
            27 : void
            28 : main::Web_Event.Click
            29 : main::Web_Event.Click
            30 : i64
            31 : void
            32 : <unknown>
            33 : {float}
            34 : void
            35 : <unknown>
            36 : <unknown>
            37 : () -> void
            l0 : main::Web_Event
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::NotAShorthandVariantOfSumType {
                        ty: i.intern("Crazy_Kool_Variant"),
                        sum_ty: Ty::Enum {
                            uid: 6,
                            variants: vec![
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Load")),
                                    uid: 0,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 0,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Unload")),
                                    uid: 1,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 1,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Key_Press")),
                                    uid: 2,
                                    sub_ty: Ty::Char.into(),
                                    discriminant: 2,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Paste")),
                                    uid: 3,
                                    sub_ty: Ty::String.into(),
                                    discriminant: 3,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Click")),
                                    uid: 5,
                                    sub_ty: Ty::ConcreteStruct {
                                        uid: 4,
                                        members: vec![
                                            MemberTy {
                                                name: hir::Name(i.intern("x")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                            MemberTy {
                                                name: hir::Name(i.intern("y")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                        ],
                                    }
                                    .into(),
                                    discriminant: 4,
                                }
                                .into(),
                            ],
                        }
                        .into(),
                    },
                    890..909,
                    None,
                ),
                (
                    TyDiagnosticKind::NotAShorthandVariantOfSumType {
                        ty: i.intern("Other_Kool_Variant"),
                        sum_ty: Ty::Enum {
                            uid: 6,
                            variants: vec![
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Load")),
                                    uid: 0,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 0,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Unload")),
                                    uid: 1,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 1,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Key_Press")),
                                    uid: 2,
                                    sub_ty: Ty::Char.into(),
                                    discriminant: 2,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Paste")),
                                    uid: 3,
                                    sub_ty: Ty::String.into(),
                                    discriminant: 3,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Click")),
                                    uid: 5,
                                    sub_ty: Ty::ConcreteStruct {
                                        uid: 4,
                                        members: vec![
                                            MemberTy {
                                                name: hir::Name(i.intern("x")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                            MemberTy {
                                                name: hir::Name(i.intern("y")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                        ],
                                    }
                                    .into(),
                                    discriminant: 4,
                                }
                                .into(),
                            ],
                        }
                        .into(),
                    },
                    1236..1255,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn switch_fully_qualified_different_enum() {
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

            Other_Enum :: enum {
                Crazy_Kool_Variant,
                Other_Kool_Variant,
            };

            foo :: () {
                clicked : Web_Event = Web_Event.Click.{
                    x = 20,
                    y = 80
                };

                switch e in clicked {
                    Web_Event.Page_Load => {
                        e;
                        1; // this is done so that the `e`s are clearly visible below
                    },
                    Web_Event.Page_Unload => {
                        e;
                        true;
                    },
                    Other_Enum.Crazy_Kool_Variant => {
                        e;
                        0.0;
                    },
                    Web_Event.Key_Press => {
                        e;
                        "";
                    },
                    Web_Event.Paste => {
                        e;
                        ' ';
                    },
                    Web_Event.Click => {
                        e;
                        e.x;
                    },
                    Other_Enum.Other_Kool_Variant => {
                        e;
                        0.0;
                    },
                }
            }
        "#,
        expect![[r#"
            main::Other_Enum : type
            main::Web_Event : type
            main::foo : () -> void
            5 : type
            6 : type
            8 : type
            10 : i64
            11 : i64
            12 : main::Web_Event.Click
            13 : main::Web_Event
            14 : type
            15 : main::Web_Event.Page_Load
            16 : main::Web_Event.Page_Load
            17 : {uint}
            18 : void
            19 : type
            20 : main::Web_Event.Page_Unload
            21 : main::Web_Event.Page_Unload
            22 : bool
            23 : void
            24 : type
            25 : main::Other_Enum.Crazy_Kool_Variant
            26 : main::Other_Enum.Crazy_Kool_Variant
            27 : {float}
            28 : void
            29 : type
            30 : type
            31 : main::Web_Event.Key_Press
            32 : str
            33 : void
            34 : type
            35 : type
            36 : main::Web_Event.Paste
            37 : char
            38 : void
            39 : type
            40 : type
            41 : main::Web_Event.Click
            42 : main::Web_Event.Click
            43 : i64
            44 : void
            45 : type
            46 : main::Other_Enum.Other_Kool_Variant
            47 : main::Other_Enum.Other_Kool_Variant
            48 : {float}
            49 : void
            50 : <unknown>
            51 : <unknown>
            52 : () -> void
            l0 : main::Web_Event
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::NotAVariantOfSumType {
                        ty: Ty::EnumVariant {
                            enum_uid: 9,
                            variant_name: hir::Name(i.intern("Crazy_Kool_Variant")),
                            uid: 7,
                            sub_ty: Ty::Void.into(),
                            discriminant: 0,
                        }
                        .into(),
                        sum_ty: Ty::Enum {
                            uid: 6,
                            variants: vec![
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Load")),
                                    uid: 0,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 0,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Unload")),
                                    uid: 1,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 1,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Key_Press")),
                                    uid: 2,
                                    sub_ty: Ty::Char.into(),
                                    discriminant: 2,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Paste")),
                                    uid: 3,
                                    sub_ty: Ty::String.into(),
                                    discriminant: 3,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Click")),
                                    uid: 5,
                                    sub_ty: Ty::ConcreteStruct {
                                        uid: 4,
                                        members: vec![
                                            MemberTy {
                                                name: hir::Name(i.intern("x")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                            MemberTy {
                                                name: hir::Name(i.intern("y")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                        ],
                                    }
                                    .into(),
                                    discriminant: 4,
                                }
                                .into(),
                            ],
                        }
                        .into(),
                    },
                    915..944,
                    None,
                ),
                (
                    TyDiagnosticKind::NotAVariantOfSumType {
                        ty: Ty::EnumVariant {
                            enum_uid: 9,
                            variant_name: hir::Name(i.intern("Other_Kool_Variant")),
                            uid: 8,
                            sub_ty: Ty::Void.into(),
                            discriminant: 1,
                        }
                        .into(),
                        sum_ty: Ty::Enum {
                            uid: 6,
                            variants: vec![
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Load")),
                                    uid: 0,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 0,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Page_Unload")),
                                    uid: 1,
                                    sub_ty: Ty::Void.into(),
                                    discriminant: 1,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Key_Press")),
                                    uid: 2,
                                    sub_ty: Ty::Char.into(),
                                    discriminant: 2,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Paste")),
                                    uid: 3,
                                    sub_ty: Ty::String.into(),
                                    discriminant: 3,
                                }
                                .into(),
                                Ty::EnumVariant {
                                    enum_uid: 6,
                                    variant_name: hir::Name(i.intern("Click")),
                                    uid: 5,
                                    sub_ty: Ty::ConcreteStruct {
                                        uid: 4,
                                        members: vec![
                                            MemberTy {
                                                name: hir::Name(i.intern("x")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                            MemberTy {
                                                name: hir::Name(i.intern("y")),
                                                ty: Ty::IInt(64).into(),
                                            },
                                        ],
                                    }
                                    .into(),
                                    discriminant: 4,
                                }
                                .into(),
                            ],
                        }
                        .into(),
                    },
                    1412..1441,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn enum_single_unused_discriminant() {
    check(
        r#"
            foo :: () {
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str | 10,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                    Unclick: struct {
                        x: i64,
                        y: i64,
                    }
                };

                clicked : Web_Event = Web_Event.Click.{x=10, y=20};
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            2 : u8
            9 : type
            11 : type
            13 : i64
            14 : i64
            15 : .Click'5
            16 : void
            17 : () -> void
            l0 : type
            l1 : enum'8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 2, Paste: str | 10, Click: struct'4 {x: i64, y: i64} | 11, Unclick: struct'6 {x: i64, y: i64} | 12}
        "#]],
        |_| [],
    )
}

#[test]
fn enum_double_unused_discriminant() {
    check(
        r#"
            foo :: () {
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str | 10,
                    Click: struct {
                        x: i64,
                        y: i64,
                    } | 10,
                    Unclick: struct {
                        x: i64,
                        y: i64,
                    }
                };

                clicked : Web_Event = Web_Event.Click.{x=10, y=20};
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            2 : u8
            6 : u8
            10 : type
            12 : type
            14 : i64
            15 : i64
            16 : .Click'5
            17 : void
            18 : () -> void
            l0 : type
            l1 : enum'8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 2, Paste: str | 10, Click: struct'4 {x: i64, y: i64} | 11, Unclick: struct'6 {x: i64, y: i64} | 12}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::DiscriminantUsedAlready { value: 10 },
                323..325,
                None,
            )]
        },
    )
}

#[test]
fn enum_single_used_discriminant() {
    check(
        r#"
            foo :: () {
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    } | 2,
                    Unclick: struct {
                        x: i64,
                        y: i64,
                    }
                };

                clicked : Web_Event = Web_Event.Click.{x=10, y=20};
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            5 : u8
            9 : type
            11 : type
            13 : i64
            14 : i64
            15 : .Click'5
            16 : void
            17 : () -> void
            l0 : type
            l1 : enum'8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 3, Paste: str | 4, Click: struct'4 {x: i64, y: i64} | 2, Unclick: struct'6 {x: i64, y: i64} | 5}
        "#]],
        |_| [],
    )
}

#[test]
fn enum_double_used_discriminant() {
    // todo: show where it was used previously
    check(
        r#"
            foo :: () {
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str | 2,
                    Click: struct {
                        x: i64,
                        y: i64,
                    } | 2,
                    Unclick: struct {
                        x: i64,
                        y: i64,
                    }
                };

                clicked : Web_Event = Web_Event.Click.{x=10, y=20};
            }
        "#,
        expect![[r#"
            main::foo : () -> void
            2 : u8
            6 : u8
            10 : type
            12 : type
            14 : i64
            15 : i64
            16 : .Click'5
            17 : void
            18 : () -> void
            l0 : type
            l1 : enum'8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 3, Paste: str | 2, Click: struct'4 {x: i64, y: i64} | 4, Unclick: struct'6 {x: i64, y: i64} | 5}
        "#]],
        |_| {
            [(
                TyDiagnosticKind::DiscriminantUsedAlready { value: 2 },
                322..323,
                None,
            )]
        },
    )
}

#[test]
fn switch_non_enum() {
    check(
        r#"
        foo :: () {
            switch e in 42 {
                i64 => 5,
                bool => 4,
                nil => 3,
            }
        }
    "#,
        expect![[r#"
            main::foo : () -> void
            0 : {uint}
            1 : type
            2 : {uint}
            3 : type
            4 : {uint}
            5 : nil
            6 : {uint}
            7 : <unknown>
            8 : <unknown>
            9 : () -> void
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::SumType,
                    found: Ty::UInt(0).into(),
                },
                45..47,
                None,
            )]
        },
    )
}

#[test]
fn enum_variants_are_not_like_distinct() {
    check(
        r#"
            Foo :: enum {
                Bar: i64,
            };

            main :: () {
                x := Foo.Bar.(5);

                x += 1;

                y : Foo.Bar = 10;
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            1 : type
            2 : i64
            3 : type
            5 : main::Foo.Bar
            6 : main::Foo.Bar
            7 : {uint}
            8 : type
            10 : {uint}
            11 : void
            12 : () -> void
            l0 : main::Foo.Bar
            l1 : main::Foo.Bar
        "#]],
        |i| {
            [
                (
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: Ty::EnumVariant {
                            enum_uid: 1,
                            variant_name: hir::Name(i.intern("Bar")),
                            uid: 0,
                            sub_ty: Ty::IInt(64).into(),
                            discriminant: 0,
                        }
                        .into(),
                        second: Ty::UInt(0).into(),
                    },
                    145..152,
                    None,
                ),
                (
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::EnumVariant {
                                enum_uid: 1,
                                variant_name: hir::Name(i.intern("Bar")),
                                uid: 0,
                                sub_ty: Ty::IInt(64).into(),
                                discriminant: 0,
                            }
                            .into(),
                        ),
                        found: Ty::UInt(0).into(),
                    },
                    184..186,
                    None,
                ),
            ]
        },
    )
}

#[test]
fn enum_variants_add() {
    // todo: make sure this also compiles correctly
    check(
        r#"
            Foo :: enum {
                Bar: i64,
            };

            main :: () {
                x := Foo.Bar.(5);

                x += Foo.Bar.(1);
                
                y : Foo.Bar = Foo.Bar.(10);
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            1 : type
            2 : i64
            3 : type
            5 : main::Foo.Bar
            6 : main::Foo.Bar
            7 : i64
            8 : type
            10 : main::Foo.Bar
            11 : type
            13 : i64
            14 : type
            16 : main::Foo.Bar
            17 : void
            18 : () -> void
            l0 : main::Foo.Bar
            l1 : main::Foo.Bar
        "#]],
        |_| [],
    )
}

#[test]
fn enum_array() {
    // todo: make sure this also compiles correctly
    check(
        r#"
            Foo :: enum {
                Bar,
                Baz: i32,
                Qux: str,
            };

            main :: () {
                arr := .[Foo.Bar, Foo.Baz.(42), Foo.Qux.("hello")];
            }
        "#,
        expect![[r#"
            main::Foo : type
            main::main : () -> void
            2 : type
            3 : type
            4 : main::Foo.Bar
            5 : i32
            6 : type
            8 : main::Foo.Baz
            9 : str
            10 : type
            12 : main::Foo.Qux
            13 : ~[3]main::Foo
            14 : void
            15 : () -> void
            l0 : ~[3]main::Foo
        "#]],
        |_| [],
    )
}

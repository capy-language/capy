use super::*;

use expect_test::expect;

#[test]
fn char_ptr_to_str() {
    check(
        r#"
            get_any :: () {
                data := char.['h', 'i', '\0'];
                ptr := ^char.(rawptr.(^data));
                str := str.(ptr);
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              16 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : char
              2 : char
              3 : char
              4 : [3]char
              5 : [3]char
              6 : ^[3]char
              8 : rawptr
              11 : ^char
              12 : ^char
              14 : str
              15 : void
              16 : main::get_any() -> void
              l0 : [3]char
              l1 : ^char
              l2 : str
        "#]],
        |_| [],
    );
}

#[test]
fn u8_ptr_to_str() {
    check(
        r#"
            get_any :: () {
                data := char.['h', 'i', '\0'];
                ptr := ^u8.(rawptr.(^data));
                str := str.(ptr);
            }
        "#,
        expect![[r#"
            main::get_any : main::get_any() -> void
              16 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : char
              2 : char
              3 : char
              4 : [3]char
              5 : [3]char
              6 : ^[3]char
              8 : rawptr
              11 : ^u8
              12 : ^u8
              14 : str
              15 : void
              16 : main::get_any() -> void
              l0 : [3]char
              l1 : ^u8
              l2 : str
        "#]],
        |_| [],
    );
}

#[test]
fn char_array_to_str() {
    check(
        r"
            get_any :: () {
                data := char.['H', 'i', '\0'];
                str := str.(data);
            }
        ",
        expect![[r#"
            main::get_any : main::get_any() -> void
              9 : main::get_any() -> void
            main::lambda#get_any : main::get_any() -> void
              1 : char
              2 : char
              3 : char
              4 : [3]char
              5 : [3]char
              7 : str
              8 : void
              9 : main::get_any() -> void
              l0 : [3]char
              l1 : str
        "#]],
        |_| [],
    );
}

#[test]
fn char() {
    check(
        r"
            foo :: () {
                my_char := 'A';
            }
        ",
        expect![[r#"
            main::foo : main::foo() -> void
              2 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : char
              1 : void
              2 : main::foo() -> void
              l0 : char
        "#]],
        |_| [],
    )
}

#[test]
fn char_as_u8() {
    check(
        r"
            foo :: () {
                my_char := 'A';
                my_u8 := u8.(my_char);
            }
        ",
        expect![[r#"
            main::foo : main::foo() -> void
              5 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : char
              1 : char
              3 : u8
              4 : void
              5 : main::foo() -> void
              l0 : char
              l1 : u8
        "#]],
        |_| [],
    )
}

#[test]
fn no_implicit_char_to_u8() {
    check(
        r"
            foo :: () {
                my_char := 'A';
                my_u8 : u8 = my_char;
            }
        ",
        expect![[r#"
            main::foo : main::foo() -> void
              4 : main::foo() -> void
            main::lambda#foo : main::foo() -> void
              0 : char
              2 : char
              3 : void
              4 : main::foo() -> void
              l0 : char
              l1 : u8
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                    found: Ty::Char.into(),
                },
                86..93,
                None,
            )]
        },
    )
}

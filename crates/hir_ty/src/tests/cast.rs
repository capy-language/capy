use super::*;

use expect_test::expect;

#[test]
fn cast() {
    check(
        r#"
            check :: () -> bool {
                num := 5;
                is_true := bool.(num);
                is_true
            };
        "#,
        expect![[r#"
            main::check : () -> bool
            1 : {uint}
            2 : {uint}
            4 : bool
            5 : bool
            6 : bool
            7 : () -> bool
            l0 : {uint}
            l1 : bool
        "#]],
        |_| [],
    );
}

#[test]
fn cast_unrelated() {
    check(
        r#"
            how_old :: () -> usize {
                name := "Gandalf";
                age := usize.(name);
                age
            };
        "#,
        expect![[r#"
            main::how_old : () -> usize
            1 : str
            2 : str
            4 : usize
            5 : usize
            6 : usize
            7 : () -> usize
            l0 : str
            l1 : usize
        "#]],
        |_| {
            [(
                TyDiagnosticKind::Uncastable {
                    from: Ty::String.into(),
                    to: Ty::UInt(u8::MAX).into(),
                },
                96..108,
                None,
            )]
        },
    );
}

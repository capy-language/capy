
use lexer::TokenKind;

use super::*;

pub(crate) fn stmt(p: &mut Parser) -> Option<CompletedMarker> {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    let res = if p.at(TokenKind::Ident) {
        variable_def(p)
    } else {
        expr::expr(p)
    };

    if res.is_some() {
        p.expect(TokenKind::Semicolon, true);
    }
    res
}

fn variable_def(p: &mut Parser) -> Option<CompletedMarker> {
    assert!(p.at(TokenKind::Ident));
    if !p.at_ahead(TokenKind::Equals) {
        return expr::expr(p);
    }

    let m = p.start();
    p.bump();

    assert!(p.at(TokenKind::Equals));
    p.bump();

    expr::expr(p);

    Some(m.complete(p, SyntaxKind::VariableDef))
}

#[cfg(test)]
mod tests {
    use crate::check;
    use expect_test::expect;

    #[test]
    fn parse_variable_definition() {
        check(
            "foo = bar",
            expect![[r#"
                Root@0..9
                  VariableDef@0..9
                    Ident@0..3 "foo"
                    Whitespace@3..4 " "
                    Equals@4..5 "="
                    Whitespace@5..6 " "
                    VariableRef@6..9
                      Ident@6..9 "bar"
                error at 6..9: expected ';'"#]],
        );
    }


    #[test]
    fn parse_variable_definition_with_semicolon() {
        check(
            "foo = bar;",
            expect![[r#"
Root@0..10
  VariableDef@0..9
    Ident@0..3 "foo"
    Whitespace@3..4 " "
    Equals@4..5 "="
    Whitespace@5..6 " "
    VariableRef@6..9
      Ident@6..9 "bar"
  Semicolon@9..10 ";""#]],
        );
    }

    #[test]
    fn recover_on_equal_sign() {
        check(
            "a =;\nb = a;",
            expect![[r#"
                Root@0..11
                  VariableDef@0..3
                    Ident@0..1 "a"
                    Whitespace@1..2 " "
                    Equals@2..3 "="
                  Semicolon@3..4 ";"
                  Whitespace@4..5 "\n"
                  VariableDef@5..10
                    Ident@5..6 "b"
                    Whitespace@6..7 " "
                    Equals@7..8 "="
                    Whitespace@8..9 " "
                    VariableRef@9..10
                      Ident@9..10 "a"
                  Semicolon@10..11 ";"
                error at 3..4: expected number, identifier, '-', '+', '(' or string, but found ';'"#]]
        )
    }
}
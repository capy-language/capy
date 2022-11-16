
mod expr;
mod stmt;

use crate::parser::marker::CompletedMarker;
use crate::parser::Parser;
use syntax::SyntaxKind;

pub(crate) fn root(p: &mut Parser) -> CompletedMarker {
    let m = p.start();

    while !p.at_end() {
        if stmt::stmt(p).is_none() {
            p.debug_kinds();
            if p.at_end() {
                break;
            }
            p.error(true);
            // todo: fix semicolon error handling.
        }
    }

    m.complete(p, SyntaxKind::Root)
}

#[cfg(test)]
mod tests {
    use crate::check;
    use expect_test::expect;

    #[test]
    fn parse_multiple_statements() {
        check(
            "a = 1;\na;",
            expect![[r#"
                Root@0..9
                  VariableDef@0..5
                    Ident@0..1 "a"
                    Whitespace@1..2 " "
                    Equals@2..3 "="
                    Whitespace@3..4 " "
                    Literal@4..5
                      Number@4..5 "1"
                  Semicolon@5..6 ";"
                  Whitespace@6..7 "\n"
                  VariableRef@7..8
                    Ident@7..8 "a"
                  Semicolon@8..9 ";""#]],
        );
    }
}
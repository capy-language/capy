
use lexer::TokenKind;

use super::*;

enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl BinaryOp {
    fn binding_power(&self) -> (u8, u8) {
        match self {
            Self::Add | Self::Sub => (1, 2),
            Self::Mul | Self::Div => (3, 4),
        }
    }
}

enum UnaryOp {
    Neg,
    Pos,
}

impl UnaryOp {
    fn binding_power(&self) -> ((), u8) {
        match self {
            Self::Neg | Self::Pos => ((), 5),
        }
    }
}

pub(super) fn expr(p: &mut Parser) -> Option<CompletedMarker> {
    expr_binding_power(p, 0)
}

fn expr_binding_power(p: &mut Parser, minimum_binding_power: u8) -> Option<CompletedMarker> {
    let mut lhs = lhs(p)?;

    loop {
        // if !p.expected_kinds.is_empty() {
        //     dbg!(&p.expected_kinds);
        //     p.expected_kinds.clear();
        // }

        let op = if p.at(TokenKind::Plus) {
            BinaryOp::Add
        } else if p.at(TokenKind::Minus) {
            BinaryOp::Sub
        } else if p.at(TokenKind::Star) {
            BinaryOp::Mul
        } else if p.at(TokenKind::Slash) {
            BinaryOp::Div
        } else {
            break;
        };

        let (left_binding_power, right_binding_power) = op.binding_power();

        if left_binding_power < minimum_binding_power {
            break;
        }

        p.bump(); // bump operator

        let m = lhs.precede(p);
        let parsed_rhs = expr_binding_power(p, right_binding_power).is_some();
        lhs = m.complete(p, SyntaxKind::InfixExpr);

        if !parsed_rhs {
            break;
        }
    }

    Some(lhs)
}

fn lhs(p: &mut Parser) -> Option<CompletedMarker> {
    let cm = if p.at(TokenKind::Number) {
        literal(p)
    } else if p.at(TokenKind::Ident) {
        variable_ref(p)
    } else if p.at(TokenKind::Minus) || p.at(TokenKind::Plus) {
        prefix_expr(p)
    } else if p.at(TokenKind::LParen) {
        paren_expr(p)
    } else {
        p.error(false);
        return None;
    };

    Some(cm)
}

fn literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Number));

    let m = p.start();
    p.bump();
    m.complete(p, SyntaxKind::Literal)
}

fn variable_ref(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Ident));

    let m = p.start();
    p.bump();
    m.complete(p, SyntaxKind::VariableRef)
}

fn prefix_expr(p: &mut Parser) -> CompletedMarker {
    let minus = p.at(TokenKind::Minus);
    let plus = p.at(TokenKind::Plus);
    assert!(minus || plus);

    let m = p.start();

    let op = if minus { UnaryOp::Neg } else { UnaryOp::Pos };
    let ((), right_binding_power) = op.binding_power();

    // Eat the operator’s token.
    p.bump();

    expr_binding_power(p, right_binding_power);

    m.complete(p, SyntaxKind::PrefixExpr)
}

fn paren_expr(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::LParen));

    let m = p.start();

    p.bump();
    expr_binding_power(p, 0);

    p.expect(TokenKind::RParen, false);

    m.complete(p, SyntaxKind::ParenExpr)
}

#[cfg(test)]
mod tests {
    use crate::check;
    use expect_test::expect;

    #[test]
    fn parse_number() {
        check(
            "123;",
            expect![[r#"
                Root@0..4
                  Literal@0..3
                    Number@0..3 "123"
                  Semicolon@3..4 ";""#]],
        )
    }

    #[test]
    fn parse_variable_ref() {
        check(
            "counter;",
            expect![[r#"
                Root@0..8
                  VariableRef@0..7
                    Ident@0..7 "counter"
                  Semicolon@7..8 ";""#]],
        )
    }

    #[test]
    fn parse_number_preceded_by_whitespace() {
        check(
            "   9876;",
            expect![[r#"
                Root@0..8
                  Whitespace@0..3 "   "
                  Literal@3..7
                    Number@3..7 "9876"
                  Semicolon@7..8 ";""#]],
        );
    }

    #[test]
    fn parse_number_followed_by_whitespace() {
        check(
            "999   ;",
            expect![[r#"
                Root@0..7
                  Literal@0..6
                    Number@0..3 "999"
                    Whitespace@3..6 "   "
                  Semicolon@6..7 ";""#]],
        );
    }

    #[test]
    fn parse_number_surrounded_by_whitespace() {
        check(
            " 123     ;",
            expect![[r#"
                Root@0..10
                  Whitespace@0..1 " "
                  Literal@1..9
                    Number@1..4 "123"
                    Whitespace@4..9 "     "
                  Semicolon@9..10 ";""#]],
        );
    }

    #[test]
    fn parse_simple_binary_expression() {
        check(
            "1+2;",
            expect![[r#"
                Root@0..4
                  InfixExpr@0..3
                    Literal@0..1
                      Number@0..1 "1"
                    Plus@1..2 "+"
                    Literal@2..3
                      Number@2..3 "2"
                  Semicolon@3..4 ";""#]],
        )
    }

    #[test]
    fn parse_left_assoc_binary_expression() {
        check(
            "1+2+3+4;",
            expect![[r#"
                Root@0..8
                  InfixExpr@0..7
                    InfixExpr@0..5
                      InfixExpr@0..3
                        Literal@0..1
                          Number@0..1 "1"
                        Plus@1..2 "+"
                        Literal@2..3
                          Number@2..3 "2"
                      Plus@3..4 "+"
                      Literal@4..5
                        Number@4..5 "3"
                    Plus@5..6 "+"
                    Literal@6..7
                      Number@6..7 "4"
                  Semicolon@7..8 ";""#]],
        )
    }

    #[test]
    fn parse_mixed_assoc_binary_expression() {
        check(
            "1+2*3-4;",
            expect![[r#"
                Root@0..8
                  InfixExpr@0..7
                    InfixExpr@0..5
                      Literal@0..1
                        Number@0..1 "1"
                      Plus@1..2 "+"
                      InfixExpr@2..5
                        Literal@2..3
                          Number@2..3 "2"
                        Star@3..4 "*"
                        Literal@4..5
                          Number@4..5 "3"
                    Minus@5..6 "-"
                    Literal@6..7
                      Number@6..7 "4"
                  Semicolon@7..8 ";""#]],
        )
    }

    #[test]
    fn parse_negation() {
        check(
            "-10;",
            expect![[r#"
                Root@0..4
                  PrefixExpr@0..3
                    Minus@0..1 "-"
                    Literal@1..3
                      Number@1..3 "10"
                  Semicolon@3..4 ";""#]],
        )
    }

    #[test]
    fn parse_positive() {
        check(
            "+10;",
            expect![[r#"
                Root@0..4
                  PrefixExpr@0..3
                    Plus@0..1 "+"
                    Literal@1..3
                      Number@1..3 "10"
                  Semicolon@3..4 ";""#]],
        )
    }

    #[test]
    fn parse_prefix_infix_precedence() {
        check(
            "-20+20;",
            expect![[r#"
                Root@0..7
                  InfixExpr@0..6
                    PrefixExpr@0..3
                      Minus@0..1 "-"
                      Literal@1..3
                        Number@1..3 "20"
                    Plus@3..4 "+"
                    Literal@4..6
                      Number@4..6 "20"
                  Semicolon@6..7 ";""#]],
        )
    }

    #[test]
    fn parse_nested_parentheses() {
        check(
            "((((((10))))));",
            expect![[r#"
                Root@0..15
                  ParenExpr@0..14
                    LParen@0..1 "("
                    ParenExpr@1..13
                      LParen@1..2 "("
                      ParenExpr@2..12
                        LParen@2..3 "("
                        ParenExpr@3..11
                          LParen@3..4 "("
                          ParenExpr@4..10
                            LParen@4..5 "("
                            ParenExpr@5..9
                              LParen@5..6 "("
                              Literal@6..8
                                Number@6..8 "10"
                              RParen@8..9 ")"
                            RParen@9..10 ")"
                          RParen@10..11 ")"
                        RParen@11..12 ")"
                      RParen@12..13 ")"
                    RParen@13..14 ")"
                  Semicolon@14..15 ";""#]],
        )
    }

    #[test]
    fn parentheses_affect_precedence() {
        check(
            "5*(2+1);",
            expect![[r#"
                Root@0..8
                  InfixExpr@0..7
                    Literal@0..1
                      Number@0..1 "5"
                    Star@1..2 "*"
                    ParenExpr@2..7
                      LParen@2..3 "("
                      InfixExpr@3..6
                        Literal@3..4
                          Number@3..4 "2"
                        Plus@4..5 "+"
                        Literal@5..6
                          Number@5..6 "1"
                      RParen@6..7 ")"
                  Semicolon@7..8 ";""#]],
        );
    }

    #[test]
    fn parse_binary_expression_with_whitespace() {
        check(
            " 1 +   2* 3 ;",
            expect![[r#"
                Root@0..13
                  Whitespace@0..1 " "
                  InfixExpr@1..12
                    Literal@1..3
                      Number@1..2 "1"
                      Whitespace@2..3 " "
                    Plus@3..4 "+"
                    Whitespace@4..7 "   "
                    InfixExpr@7..12
                      Literal@7..8
                        Number@7..8 "2"
                      Star@8..9 "*"
                      Whitespace@9..10 " "
                      Literal@10..12
                        Number@10..11 "3"
                        Whitespace@11..12 " "
                  Semicolon@12..13 ";""#]],
        );
    }

    #[test]
    fn parse_unclosed_parentheses() {
        check(
            "(foo;",
            expect![[r#"
                Root@0..5
                  ParenExpr@0..4
                    LParen@0..1 "("
                    VariableRef@1..4
                      Ident@1..4 "foo"
                  Semicolon@4..5 ";"
                error at 4..5: expected '+', '-', '*', '/' or ')', but found ';'"#]],
        );
    }

    #[test]
    fn do_not_parse_operator_if_getting_rhs_failed() {
        check(
            "(1+",
            expect![[r#"
                Root@0..3
                  ParenExpr@0..3
                    LParen@0..1 "("
                    InfixExpr@1..3
                      Literal@1..2
                        Number@1..2 "1"
                      Plus@2..3 "+"
                error at 2..3: expected number, identifier, '-', '+' or '('
                error at 2..3: expected ')'
                error at 2..3: expected ';'"#]],
        );
    }
}

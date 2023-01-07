
use syntax::TokenKind;

use crate::{grammar::{path::parse_path, types::{parse_type, parse_type_annotation}}, token_set::TokenSet};

use super::*;

pub(super) fn parse_expr(
    p: &mut Parser,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    parse_expr_bp(p, 0, TokenSet::NONE, expected_syntax_name)
}

// bp stands for binding power
// look at online resources for more
fn parse_expr_bp(
    p: &mut Parser, 
    minimum_bp: u8,
    recovery_set: TokenSet,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    let mut lhs = parse_lhs(p, recovery_set, expected_syntax_name)?;

    loop {
        let (left_bp, right_bp) = if p.at(TokenKind::Plus) || p.at(TokenKind::Hyphen) {
            (1, 2)
        } else if p.at(TokenKind::Asterisk) || p.at(TokenKind::Slash) {
            (3, 4)
        } else {
            break;
        };

        if left_bp < minimum_bp {
            break;
        }

        p.bump(); // bump operator

        let m = lhs.precede(p);
        parse_expr_bp(p, right_bp, recovery_set, "operand");
        lhs = m.complete(p, NodeKind::BinaryExpr);
    }

    Some(lhs)
}

fn parse_lhs(
    p: &mut Parser,
    recovery_set: TokenSet,
    expected_syntax_name: &'static str,
) -> Option<CompletedMarker> {
    let _guard = p.expected_syntax_name(expected_syntax_name);

    let cm = if p.at(TokenKind::Int) {
        parse_int_literal(p)
    } else if p.at(TokenKind::Quote) {
        parse_string_literal(p)
    } else if p.at(TokenKind::Ident) {
        parse_ref_or_call(p)
    } else if p.at(TokenKind::Hyphen) || p.at(TokenKind::Plus) {
        parse_prefix_expr(p, recovery_set)
    } else if p.at(TokenKind::LParen) {
        parse_lambda_expr(p, recovery_set)
    } else if p.at(TokenKind::LBrace) {
        parse_block_expr(p)
    } else {
        return p.error_with_recovery_set(recovery_set);
    };

    Some(cm)
}

fn parse_int_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Int));
    let m = p.start();
    p.bump();
    m.complete(p, NodeKind::IntLiteral)
}

fn parse_string_literal(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::Quote));
    let m = p.start();
    p.bump();

    while p.at(TokenKind::StringContents) || p.at(TokenKind::Escape) {
        p.bump();
    }

    p.expect(TokenKind::Quote);
    m.complete(p, NodeKind::StringLiteral)
}

fn parse_ref_or_call(
    p: &mut Parser
) -> CompletedMarker {
    assert!(p.at(TokenKind::Ident));
    let m = p.start();
    parse_path(p, TokenSet::NONE);

    if p.at(TokenKind::LParen) {
        let arg_list_m = p.start();
    
        p.bump();

        // collect arguments
        loop {
            if p.at(TokenKind::RParen) {
                break;
            }
            if let Some(arg_m) = expr::parse_expr(p, "argument") {
                arg_m.precede(p).complete(p, NodeKind::Arg);
            }
            if !p.at(TokenKind::RParen) {
                p.expect_with_no_skip(TokenKind::Comma);
            }
        }

        p.expect(TokenKind::RParen);

        arg_list_m.complete(p, NodeKind::ArgList);
        m.complete(p, NodeKind::Call)
    } else {
        m.complete(p, NodeKind::Ref)
    }
}

fn parse_prefix_expr(
    p: &mut Parser,
    recovery_set: TokenSet
) -> CompletedMarker {
    let minus = p.at(TokenKind::Hyphen);
    let plus = p.at(TokenKind::Plus);
    assert!(minus || plus);

    let m = p.start();

    let right_bp = if plus || minus {
        5
    } else {
        unreachable!()
    };

    // Eat the operator’s token.
    p.bump();
    parse_expr_bp(p, right_bp, recovery_set, "operand");
    m.complete(p, NodeKind::UnaryExpr)
}

fn paren_expr(
    p: &mut Parser,
    recovery_set: TokenSet
) -> CompletedMarker {
    assert!(p.at(TokenKind::LParen));

    let m = p.start();

    p.bump();
    parse_expr_bp(p, 0, recovery_set, "expression");

    p.expect(TokenKind::RParen);

    m.complete(p, NodeKind::ParenExpr)
}

const LAMBDA_EXPECTED: TokenSet = TokenSet::new([
    TokenKind::Ident,
    TokenKind::Dot,
    TokenKind::Colon,
    TokenKind::Whitespace,
]);

fn parse_lambda_expr(
    p: &mut Parser,
    recovery_set: TokenSet,
) -> CompletedMarker {
    assert!(p.at(TokenKind::LParen));

    let mut closed_paren = false;
    let saved_idx = p.token_idx;
    loop {
        p.token_idx += 1;
        let kind = p.peek();
        if kind.is_none() { 
            p.token_idx = saved_idx;
            return paren_expr(p, recovery_set); 
        }
        let kind = kind.unwrap();

        if TokenSet::new([TokenKind::Colon, TokenKind::Comma, TokenKind::Arrow]).contains(kind) {
            p.token_idx = saved_idx;
            break;
        } else if kind == TokenKind::RParen {
            closed_paren = true;
        } else if kind == TokenKind::LBrace || kind == TokenKind::RBrace {
            p.token_idx = saved_idx;
            if closed_paren {
                break;
            } else {
                return paren_expr(p, recovery_set);
            }
        } else if !LAMBDA_EXPECTED.contains(kind) {
            println!("Found unexpected token {:?}", kind);
            p.token_idx = saved_idx;
            return paren_expr(p, recovery_set);
        }
    }

    let m = p.start();

    let param_list_m = p.start();

    p.bump();

    while p.at(TokenKind::Ident) {
        let param_m = p.start();
        p.bump();
        parse_type_annotation(p, TokenSet::new([TokenKind::Comma, TokenKind::RParen]), "parameter type");
        param_m.complete(p, NodeKind::Param);

        if p.at_ahead(1, TokenKind::Ident) {
            p.expect_with_no_skip(TokenKind::Comma);
        } else {
            break;
        }
    }
    p.expect(TokenKind::RParen);

    param_list_m.complete(p, NodeKind::ParamList);

    if p.at(TokenKind::Arrow) {
        p.bump();
        let _guard = p.expected_syntax_name("return type");
        parse_type(p, TokenSet::new([TokenKind::LBrace]));
    }

    if p.at(TokenKind::LBrace) {
        parse_block_expr(p);
    } else {
        let _guard = p.expected_syntax_name("lambda body");
        p.error();
    }

    m.complete(p, NodeKind::Lambda)
}

fn parse_block_expr(p: &mut Parser) -> CompletedMarker {
    assert!(p.at(TokenKind::LBrace));

    let m = p.start();
    p.bump();

    while !p.at(TokenKind::RBrace) {
        stmt::stmt(p);
    }

    p.expect(TokenKind::RBrace);

    m.complete(p, NodeKind::Block)
}

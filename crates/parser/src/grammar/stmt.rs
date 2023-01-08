
use syntax::TokenKind;

use crate::{token_set::TokenSet, grammar::types::parse_type_annotation};

use super::{*, expr::parse_expr};

const DEF_TOKENS: TokenSet = TokenSet::new([
    TokenKind::Equals, 
    TokenKind::Colon,
]);

pub(crate) fn parse_stmt(p: &mut Parser) -> Option<CompletedMarker> {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    let _guard = p.expected_syntax_name("statement");

    let (cm, is_expr) = if p.at(TokenKind::Ident) {
        println!("parse_var_def");
        parse_var_def(p)
    } else {
        (None, true)
    };

    // if the definition was actually just an expression, let's move on
    if !is_expr {
        println!("return expr");
        if cm.is_some() {
            p.expect_with_no_skip(TokenKind::Semicolon);
        }
        return cm;
    }

    let cm = match cm {
        Some(expr) => expr,
        None => { 
            println!("parse_expr");
            parse_expr(p, "statement")? 
        }
    };

    if p.at(TokenKind::RBrace) || p.at_eof() {
        println!("returning at end");
        return Some(cm);
    }

    let m = cm.precede(p);
    let res = Some(m.complete(p, NodeKind::ExprStmt));

    println!("returning at semicolon");
    p.expect_with_no_skip(TokenKind::Semicolon);
    res
}

pub(crate) fn parse_def(p: &mut Parser) -> CompletedMarker {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    let _guard = p.expected_syntax_name("statement");

    let m = p.start();
    p.expect(TokenKind::Ident);

    if p.at(TokenKind::Colon) {
        parse_type_annotation(p, TokenSet::new([TokenKind::Equals]), "variable type");
    }

    p.expect(TokenKind::Equals);

    expr::parse_expr(p, "value");

    m.complete(p, NodeKind::VarDef)
}

fn parse_var_def(p: &mut Parser) -> (Option<CompletedMarker>, bool) {
    assert!(p.at(TokenKind::Ident));
    if !p.at_set_ahead(1, DEF_TOKENS) {
        return (expr::parse_expr(p, "statement"), true)
    }

    let m = p.start();
    p.bump();

    if p.at(TokenKind::Colon) {
        parse_type_annotation(p, TokenSet::new([TokenKind::Equals]), "variable type");
    }

    p.expect(TokenKind::Equals);

    expr::parse_expr(p, "value");

    (Some(m.complete(p, NodeKind::VarDef)), false)
}
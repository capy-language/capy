
use syntax::TokenKind;

use crate::{token_set::TokenSet, grammar::types::parse_type_annotation};

use super::*;

const DEF_TOKENS: TokenSet = TokenSet::new([
    TokenKind::Equals, 
    TokenKind::Colon,
]);

pub(crate) fn stmt(p: &mut Parser) -> Option<CompletedMarker> {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    let _guard = p.expected_syntax_name("statement");

    let res = if p.at(TokenKind::Ident) {
        parse_var_def(p) // function itself handles variable refs
    } else if p.at(TokenKind::Return) {
        return_val(p)
    } else {
        expr::parse_expr(p, "statement")
            .map(|expr| 
                expr
                    .precede(p)
                    .complete(p, NodeKind::ExprStmt))
    };

    if res.is_some() {
        p.expect(TokenKind::Semicolon);
    }
    res
}

pub(crate) fn stmt_def_only(p: &mut Parser) -> Option<CompletedMarker> {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    let _guard = p.expected_syntax_name("definition");

    let res = if p.at(TokenKind::Ident) {
        parse_var_def(p) // function itself handles variable refs
    } else {
        None
    };

    if res.is_some() {
        p.expect(TokenKind::Semicolon);
    }
    res
}

fn return_val(p: &mut Parser) -> Option<CompletedMarker> {
    assert!(p.at(TokenKind::Return));

    let m = p.start();
    p.bump();

    if !p.at(TokenKind::Semicolon) {
        expr::parse_expr(p, "value");
    }

    Some(m.complete(p, NodeKind::ReturnFlow))
}

fn parse_var_def(p: &mut Parser) -> Option<CompletedMarker> {
    assert!(p.at(TokenKind::Ident));
    if !p.at_set_ahead(1, DEF_TOKENS) {
        return expr::parse_expr(p, "statement")
            .map(|expr| 
                expr
                    .precede(p)
                    .complete(p, NodeKind::ExprStmt));
    }

    let m = p.start();
    p.bump();

    if p.at(TokenKind::Colon) {
        parse_type_annotation(p, TokenSet::new([TokenKind::Equals]), "variable type");
    }

    p.expect(TokenKind::Equals);

    expr::parse_expr(p, "value");

    Some(m.complete(p, NodeKind::VarDef))
}
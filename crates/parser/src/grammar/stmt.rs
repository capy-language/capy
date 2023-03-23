use syntax::TokenKind;

use crate::{grammar::ty::parse_ty, token_set::TokenSet};

use super::*;

const DEF_QUALIFIERS: TokenSet = TokenSet::new([TokenKind::Equals, TokenKind::Colon]);

/// this function would only be called in a REPL or code block
pub(crate) fn parse_stmt(p: &mut Parser) -> Option<CompletedMarker> {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }
    if p.at_eof() {
        return None;
    }

    let _guard = p.expected_syntax_name("statement");

    // Idents can start expressions AND definitions
    // this code tells the difference by looking ahead
    if p.at(TokenKind::Mut) || (p.at(TokenKind::Ident) && p.at_ahead(1, DEF_QUALIFIERS)) {
        let res = Some(parse_def(p, true));
        p.expect_with_no_skip(TokenKind::Semicolon);
        return res;
    }

    // now we know that it's just an expression
    let expr_cm = expr::parse_expr(p, "statement")?;

    // return block tail expressions
    if p.at(TokenKind::RBrace) {
        return Some(expr_cm);
    }

    let m = expr_cm.precede(p);
    let res = Some(m.complete(p, NodeKind::ExprStmt));

    if !p.at_eof() {
        p.expect_with_no_skip(TokenKind::Semicolon);
    }

    res
}

pub(crate) fn parse_def(p: &mut Parser, allow_set: bool) -> CompletedMarker {
    let _guard = p.expected_syntax_name("statement");

    let m = p.start();

    let allow_set = if p.at(TokenKind::Mut) {
        p.bump();
        false
    } else {
        allow_set
    };

    p.expect(TokenKind::Ident);

    let def = if !allow_set || p.at(TokenKind::Colon) {
        p.expect_with_no_skip(TokenKind::Colon);
        if !p.at(TokenKind::Equals) {
            let _guard = p.expected_syntax_name("defined type");
            parse_ty(p, TokenSet::new([TokenKind::Equals]));
        }
        true
    } else {
        false
    };

    p.expect(TokenKind::Equals);

    expr::parse_expr(p, "value");

    m.complete(
        p,
        if def {
            NodeKind::VarDef
        } else {
            NodeKind::VarSet
        },
    )
}

use syntax::TokenKind;

use crate::token_set::TokenSet;

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
    if p.at(TokenKind::Ident) && p.at_ahead(1, TokenSet::new([TokenKind::Colon])) {
        let res = Some(parse_def(p));
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

    let res = if p.at(TokenKind::Equals) {
        // make the other expression a source, and then surround it with an assignment
        let m = m.complete(p, NodeKind::Source).precede(p);

        p.bump();

        expr::parse_expr(p, "value");

        Some(m.complete(p, NodeKind::Assign))
    } else {
        Some(m.complete(p, NodeKind::ExprStmt))
    };

    if !p.at_eof() {
        p.expect_with_no_skip(TokenKind::Semicolon);
    }

    res
}

enum Def {
    Binding,
    Variable,
}

pub(crate) fn parse_def(p: &mut Parser) -> CompletedMarker {
    let _guard = p.expected_syntax_name("statement");

    let m = p.start();

    p.expect(TokenKind::Ident);

    p.expect_with_no_skip(TokenKind::Colon);

    const DEF_SET: TokenSet = TokenSet::new([TokenKind::Equals, TokenKind::Colon]);
    if !p.at_set(DEF_SET) {
        expr::parse_ty(p, "type annotation", DEF_SET);
    }

    let def = if p.at(TokenKind::Colon) {
        p.expect(TokenKind::Colon);
        Def::Binding
    } else {
        p.expect(TokenKind::Equals);
        Def::Variable
    };

    expr::parse_expr(p, "value");

    m.complete(
        p,
        match def {
            Def::Binding => NodeKind::Binding,
            Def::Variable => NodeKind::VarDef,
        },
    )
}

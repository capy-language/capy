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
    if p.at(TokenKind::Ident) && p.at_ahead(1, DEF_QUALIFIERS) {
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

enum Def {
    Binding,
    Variable,
    Assignment,
}

pub(crate) fn parse_def(p: &mut Parser, allow_set: bool) -> CompletedMarker {
    let _guard = p.expected_syntax_name("statement");

    let m = p.start();

    p.expect(TokenKind::Ident);

    let def = if !allow_set || p.at(TokenKind::Colon) {
        p.expect_with_no_skip(TokenKind::Colon);

        let def_set = TokenSet::new([TokenKind::Equals, TokenKind::Colon]);
        if !p.at_set(def_set) {
            expr::parse_ty(p, "type annotation", def_set);
        }

        if p.at(TokenKind::Colon) {
            p.expect(TokenKind::Colon);
            Def::Binding
        } else {
            p.expect(TokenKind::Equals);
            Def::Variable
        }
    } else {
        p.expect(TokenKind::Equals);

        Def::Assignment // todo: parse assignments to expressions. e.g. my_var^ = 4; my_array[8] = 15;
    };

    expr::parse_expr(p, "value");

    m.complete(
        p,
        match def {
            Def::Binding => NodeKind::Binding,
            Def::Variable => NodeKind::VarDef,
            Def::Assignment => NodeKind::Assign,
        },
    )
}

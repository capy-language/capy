use syntax::TokenKind;

use crate::token_set::TokenSet;

use super::*;

/// this function would only be called in a REPL or code block
pub(crate) fn parse_stmt(p: &mut Parser, repl: bool) -> Option<CompletedMarker> {
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
        let (res, _) = parse_def(p, false);
        p.expect_with_no_skip(TokenKind::Semicolon);
        while p.at(TokenKind::Semicolon) {
            p.bump();
        }
        return Some(res);
    }

    // now we know that it's just an expression
    let expr_cm = expr::parse_expr(p, "statement")?;

    // return block tail expressions
    if p.at(TokenKind::RBrace) {
        return Some(expr_cm);
    }

    let m = expr_cm.precede(p);

    let (res, requires_semicolon) = if p.at(TokenKind::Equals) {
        // make the other expression a source, and then surround it with an assignment
        let m = m.complete(p, NodeKind::Source).precede(p);

        p.bump();

        expr::parse_expr(p, "value");

        (Some(m.complete(p, NodeKind::Assign)), true)
    } else {
        let requires_semicolon = !matches!(
            expr_cm.kind(),
            NodeKind::IfExpr | NodeKind::WhileExpr | NodeKind::Block
        );

        (Some(m.complete(p, NodeKind::ExprStmt)), requires_semicolon)
    };

    if !(repl && p.at_eof()) && requires_semicolon {
        p.expect_with_no_skip(TokenKind::Semicolon);
    }
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    res
}

#[derive(PartialEq)]
enum DefMutability {
    Binding,
    Variable,
}

/// returns the completed marker for the definition, and a bool if it is a top level lambda definition
pub(crate) fn parse_def(p: &mut Parser, top_level: bool) -> (CompletedMarker, bool) {
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
        DefMutability::Binding
    } else {
        p.expect(TokenKind::Equals);
        DefMutability::Variable
    };

    let value = expr::parse_expr(p, "value");

    (
        m.complete(
            p,
            match def {
                DefMutability::Binding => NodeKind::Binding,
                DefMutability::Variable => NodeKind::VarDef,
            },
        ),
        top_level
            && value
                .map(|value| value.kind() == NodeKind::Lambda)
                .unwrap_or_default()
            && p.previous_token_kind() != TokenKind::Extern,
    )
}

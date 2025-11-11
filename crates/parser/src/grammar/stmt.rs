use syntax::TokenKind;

use crate::token_set::TokenSet;

use super::*;

// this is not a list of ALL the binary operators,
// just the ones that work with quick assignment
pub(crate) const QUICK_ASSIGN_OPERATORS: TokenSet = TokenSet::new([
    TokenKind::Plus,
    TokenKind::Hyphen,
    TokenKind::Pipe,
    TokenKind::Tilde,
    TokenKind::Asterisk,
    TokenKind::Slash,
    TokenKind::Percent,
    TokenKind::And,
    TokenKind::DoubleLeft,
    TokenKind::DoubleRight,
]);

/// this function would only be called in a REPL or code block
pub(crate) fn parse_stmt(p: &mut Parser, repl: bool) -> Option<CompletedMarker> {
    while p.at(TokenKind::Semicolon) {
        p.bump();
    }
    // we don't check for p.at_default_recovery_set(), because statements can be expressions
    // and expressions can start with '{' or '}'
    if p.at_eof() {
        return None;
    }

    let _guard = p.expected_syntax_name("statement");

    let at_return = p.at(TokenKind::Return);
    let at_break = p.at(TokenKind::Break);
    let at_continue = p.at(TokenKind::Continue);
    let at_defer = p.at(TokenKind::Defer);
    if at_return || at_break || at_continue || at_defer {
        let m = p.start();
        p.bump();

        let old_label_syntax =
            p.at(TokenKind::Ident) && p.at_ahead(1, TokenSet::new([TokenKind::Backtick]));
        let new_label_syntax = p.at(TokenKind::Backtick)
            && p.at_ahead(1, TokenSet::new([TokenKind::Ident]))
            && !p.at_ahead(2, TokenSet::new([TokenKind::Colon]));

        if !at_return && (old_label_syntax || new_label_syntax) {
            let label = p.start();
            p.expect_with_no_skip(TokenKind::Backtick);
            p.expect_with_no_skip(TokenKind::Ident);
            if old_label_syntax && p.at(TokenKind::Backtick) {
                let _guard = p.expected_syntax_name("nothing");
                p.error_with_skip();
            }
            label.complete(p, NodeKind::LabelRef);
        }

        if at_defer {
            expr::parse_expr(p, "defer expression");
        }

        if (at_return || at_break) && !p.at(TokenKind::Semicolon) {
            expr::parse_expr(
                p,
                if at_break {
                    "break value"
                } else {
                    "return value"
                },
            );
        }

        p.expect_with_no_skip(TokenKind::Semicolon);

        let res = m.complete(
            p,
            if at_return {
                NodeKind::ReturnStmt
            } else if at_break {
                NodeKind::BreakStmt
            } else if at_continue {
                NodeKind::ContinueStmt
            } else {
                NodeKind::DeferStmt
            },
        );

        while p.at(TokenKind::Semicolon) {
            p.bump();
        }

        return Some(res);
    }

    // Idents can start expressions AND definitions
    // this code tells the difference by looking ahead
    if p.at(TokenKind::Ident) && p.at_ahead(1, TokenSet::new([TokenKind::Colon])) {
        let res = parse_decl(p, false);
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

    let quick_assign =
        p.at_set(QUICK_ASSIGN_OPERATORS) && p.at_ahead(1, TokenSet::new([TokenKind::Equals]));
    let regular_assign = p.at(TokenKind::Equals);
    let res = if quick_assign || regular_assign {
        // make the other expression a source, and then surround it with an assignment
        let m = m.complete(p, NodeKind::Source).precede(p);

        if quick_assign {
            // bump the operator
            p.bump();
        }
        p.bump();

        expr::parse_expr(p, "value");

        if !(repl && p.at_eof()) {
            p.expect_with_no_skip(TokenKind::Semicolon);
        }

        Some(m.complete(p, NodeKind::Assign))
    } else {
        if !(matches!(
            expr_cm.kind(),
            NodeKind::IfExpr
                | NodeKind::WhileExpr
                | NodeKind::SwitchExpr
                | NodeKind::ComptimeExpr
                | NodeKind::Block
        ) || (repl && p.at_eof()))
        {
            p.expect_with_no_skip(TokenKind::Semicolon);
        }

        Some(m.complete(p, NodeKind::ExprStmt))
    };

    while p.at(TokenKind::Semicolon) {
        p.bump();
    }

    res
}

pub(crate) fn parse_decl(p: &mut Parser, top_level: bool) -> CompletedMarker {
    let m = p.start();

    // todo: this is not very descriptive, but i don't think "variable name" fits either
    let _guard = p.expected_syntax_name("name");
    p.expect_with_no_skip(TokenKind::Ident);

    let first_colon = p.at(TokenKind::Colon);
    p.expect_with_no_skip(TokenKind::Colon);

    const DEF_SET: TokenSet = TokenSet::new([TokenKind::Equals, TokenKind::Colon]);
    if first_colon && !p.at_set(DEF_SET) {
        expr::parse_ty(p, "type annotation", DEF_SET);
    }

    if p.at_eof() || p.at(TokenKind::Semicolon) {
        p.expect_with_no_skip(TokenKind::Semicolon);
        return m.complete(p, NodeKind::VarDef);
    }

    let def_kind = if top_level || p.at(TokenKind::Colon) {
        // if there is an equal sign skip it, otherwise don't skip anything
        p.expect_with_recovery_set(TokenKind::Colon, TokenSet::ALL.without(TokenKind::Equals));
        NodeKind::Binding
    } else {
        p.expect_with_no_skip(TokenKind::Equals);
        NodeKind::VarDef
    };

    // This catches global declarations that have "extern" as a value.
    // e.g.
    // ```
    // hello :: extern;
    // ```
    if top_level && p.at(TokenKind::Extern) {
        p.bump();
        p.expect_with_no_skip(TokenKind::Semicolon);
        return m.complete(p, def_kind);
    }

    let value = expr::parse_expr(p, "value");

    let top_level_extern_lambda = top_level
        && value.is_some_and(|value| value.kind() == NodeKind::Lambda)
        && p.previous_token_kind() == TokenKind::RBrace;

    if !top_level_extern_lambda {
        p.expect_with_no_skip(TokenKind::Semicolon);
    }

    m.complete(p, def_kind)
}

mod expr;
mod stmt;

use syntax::{NodeKind, TokenKind};

use crate::parser::marker::CompletedMarker;
use crate::parser::Parser;
use crate::token_set::TokenSet;

pub(crate) fn source_file(p: &mut Parser<'_>) {
    let m = p.start();

    while !p.at_eof() {
        // just skip over semicolons
        if p.at(TokenKind::Semicolon) {
            p.bump();
            continue;
        }
        // if we didn't get a semicolon, we definitely shouldn't be getting something else from the default recovery set
        if p.at_default_recovery_set() {
            let _guard = p.expected_syntax_name("definition");
            p.error_with_recovery_set_no_default(TokenSet::NONE);
            continue;
        }
        let (_, lambda_def) = stmt::parse_def(p, true);
        if !lambda_def {
            p.expect_with_no_skip(TokenKind::Semicolon);
        }
    }

    m.complete(p, NodeKind::Root);
}

pub(crate) fn repl_line(p: &mut Parser<'_>) {
    let m = p.start();

    while !p.at_eof() {
        if p.at(TokenKind::Semicolon) {
            p.bump();
        } else if stmt::parse_stmt(p, true).is_none() {
            if p.at_eof() {
                break;
            }
            let _guard = p.expected_syntax_name("statement");
            p.error_with_skip();
        }
    }

    m.complete(p, NodeKind::Root);
}

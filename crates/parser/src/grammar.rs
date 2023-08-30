mod expr;
mod stmt;

use syntax::{NodeKind, TokenKind};

use crate::parser::marker::CompletedMarker;
use crate::parser::Parser;

pub(crate) fn source_file(p: &mut Parser<'_>) {
    let m = p.start();

    while !p.at_eof() {
        if p.at(TokenKind::Semicolon) {
            p.bump();
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


mod path;
mod expr;
mod stmt;
mod types;

use syntax::{NodeKind, TokenKind};

use crate::parser::marker::CompletedMarker;
use crate::parser::Parser;

pub(crate) fn source_file(p: &mut Parser<'_>) {
    let m = p.start();

    while !p.at_eof() {
        stmt::parse_def(p);
    }

    m.complete(p, NodeKind::Root);
}

pub(crate) fn repl_line(p: &mut Parser<'_>) {
    let m = p.start();

    while !p.at_eof() {
        if p.at(TokenKind::RBrace) || p.at(TokenKind::Semicolon) {
            let _guard = p.expected_syntax_name("definition or statement");
            p.error_without_skip();
        } else if stmt::parse_stmt(p).is_none() {
            if p.at_eof() {
                break;
            }
            let _guard = p.expected_syntax_name("definition or statement");
            p.error_with_skip();
        }
    }

    m.complete(p, NodeKind::Root);
}

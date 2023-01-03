use syntax::{NodeKind, TokenKind};

use crate::{parser::{Parser, marker::CompletedMarker}, token_set::TokenSet};

use super::path::parse_path;

pub(super) fn parse_type(
    p: &mut Parser<'_>,
    recovery_set: TokenSet,
) -> CompletedMarker {
    let m = p.start();
    parse_path(p, recovery_set);
    m.complete(p, NodeKind::Type)
}

pub(super) fn parse_type_annotation(
    p: &mut Parser<'_>,
    recovery_set: TokenSet,
    expected_syntax_name: &'static str
) -> CompletedMarker {
    p.expect_with_recovery_set(TokenKind::Colon, recovery_set);

    let m = p.start();

    let _guard = p.expected_syntax_name(expected_syntax_name);
    parse_path(p, recovery_set);

    m.complete(p, NodeKind::Type)
}
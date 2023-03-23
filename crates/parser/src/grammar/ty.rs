use syntax::{NodeKind, TokenKind};

use crate::{
    parser::{marker::CompletedMarker, Parser},
    token_set::TokenSet,
};

use super::path::parse_path;

pub(super) fn parse_ty(p: &mut Parser<'_>, recovery_set: TokenSet) -> CompletedMarker {
    if p.at(TokenKind::LBrack) {
        let array_m = p.start();
        p.bump();

        let guard = p.expected_syntax_name("array size");
        let size = p.start();
        p.expect_with_no_skip(TokenKind::Int);
        size.complete(p, NodeKind::IntLiteral);
        drop(guard);

        p.expect_with_no_skip(TokenKind::RBrack);

        parse_ty(p, recovery_set);

        array_m.complete(p, NodeKind::ArrayTy)
    } else {
        let path_m = p.start();
        parse_path(p, recovery_set);
        path_m.complete(p, NodeKind::NamedTy)
    }
}

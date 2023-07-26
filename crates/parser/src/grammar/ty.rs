use syntax::NodeKind;

use crate::{
    parser::{marker::CompletedMarker, Parser},
    token_set::TokenSet,
};

use super::expr::parse_expr_with_recovery_set;

pub(super) fn parse_ty(
    p: &mut Parser<'_>,
    expected_syntax_name: &'static str,
    recovery_set: TokenSet,
) -> CompletedMarker {
    let path_m = p.start();
    parse_expr_with_recovery_set(p, expected_syntax_name, recovery_set);
    path_m.complete(p, NodeKind::Ty)
}

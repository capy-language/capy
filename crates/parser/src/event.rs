
use syntax::SyntaxKind;
use crate::parser::ParseError;

#[derive(Debug, PartialEq)]
pub(crate) enum Event {
    StartNode {
        kind: SyntaxKind,
        forward_parent: Option<usize>,
    },
    AddToken,
    FinishNode,
    Error(ParseError),
    Placeholder,
}

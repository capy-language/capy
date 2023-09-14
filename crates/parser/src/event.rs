use syntax::NodeKind;

#[derive(Debug, Clone, Copy)]
pub(crate) enum Event {
    StartNode { kind: NodeKind },
    FinishNode,
    AddToken,
}

static_assertions::assert_eq_size!(Event, Option<Event>, u8);

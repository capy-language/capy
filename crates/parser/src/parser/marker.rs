use drop_bomb::DropBomb;
use syntax::NodeKind;

use crate::event::Event;

use super::Parser;

pub(crate) struct Marker {
    start_token_idx: usize,
    pos: usize,
    bomb: DropBomb,
}

impl Marker {
    pub(crate) fn new(pos: usize, start_token_idx: usize) -> Self {
        Self {
            start_token_idx,
            pos,
            bomb: DropBomb::new("Markers need to be completed"),
        }
    }

    pub(crate) fn complete(mut self, p: &mut Parser<'_>, kind: NodeKind) -> CompletedMarker {
        self.bomb.defuse();
        let old_event = p.events[self.pos].replace(Event::StartNode { kind });
        debug_assert!(old_event.is_none());
        p.events.push(Some(Event::FinishNode));

        CompletedMarker {
            kind,
            start_token_idx: self.start_token_idx,
            pos: self.pos,
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) struct CompletedMarker {
    kind: NodeKind,
    start_token_idx: usize,
    pos: usize,
}

impl CompletedMarker {
    pub(crate) fn kind(&self) -> NodeKind {
        self.kind
    }

    pub(crate) fn start_token_idx(&self) -> usize {
        self.start_token_idx
    }

    pub(crate) fn precede(self, p: &mut Parser) -> Marker {
        p.events.insert(self.pos, None);
        Marker::new(self.pos, self.start_token_idx)
    }
}

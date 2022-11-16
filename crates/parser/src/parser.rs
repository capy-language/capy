
pub(crate) mod marker;

mod parse_error;
use std::mem;

pub(crate) use parse_error::ParseError;

use crate::event::Event;
use crate::grammar;
use crate::source::Source;

use marker::Marker;

use lexer::{Token, TokenKind};
use syntax::SyntaxKind;

const RECOVERY_SET: [TokenKind; 1] = [TokenKind::Semicolon];

pub(crate) struct Parser<'t, 'input> {
    source: Source<'t, 'input>,
    events: Vec<Event>,
    expected_kinds: Vec<TokenKind>,
}

impl<'t, 'input> Parser<'t, 'input> {
    pub(crate) fn new(source: Source<'t, 'input>) -> Self {
        Self {
            source,
            events: Vec::new(),
            expected_kinds: Vec::new(),
        }
    }

    pub(crate) fn parse(mut self) -> Vec<Event> {
        grammar::root(&mut self);

        self.events
    }

    pub(crate) fn expect(&mut self, kind: TokenKind, clear: bool) {
        if clear {
            self.expected_kinds.clear();
        }
        if self.at(kind) {
            self.bump();
        } else {
            self.error(false);
        }
    }

    pub(crate) fn error(&mut self, move_past_recovery: bool) {
        let current_token = self.peek_token();

        let (found, range) = if let Some(Token { kind, range, .. }) = current_token {
            (Some(*kind), *range)
        } else {
            (None, self.source.last_token_range().unwrap())
        };

        self.events.push(Event::Error(ParseError {
            expected: mem::take(&mut self.expected_kinds),
            found,
            range,
        }));

        if !self.at_end() {
            if self.at_set(&RECOVERY_SET) && move_past_recovery {
                self.bump();
            } else {
                let m = self.start();
                while !self.at_set(&RECOVERY_SET) && !self.at_end() {
                    self.bump();
                }
                m.complete(self, SyntaxKind::Error);
            }
        }
    }

    fn peek(&mut self) -> Option<TokenKind> {
        self.source.peek_kind(0)
    }

    fn peek_ahead(&mut self) -> Option<TokenKind> {
        self.source.peek_kind(1)
    }

    pub(crate) fn peek_token(&mut self) -> Option<&Token> {
        self.source.peek_token(0)
    }

    pub(crate) fn bump(&mut self) {
        self.expected_kinds.clear();
        self.source.next_token().unwrap();
        self.events.push(Event::AddToken)
    }

    pub(crate) fn start(&mut self) -> Marker {
        let pos = self.events.len();
        self.events.push(Event::Placeholder);

        Marker::new(pos)
    }

    pub(crate) fn at(&mut self, kind: TokenKind) -> bool {
        self.expected_kinds.push(kind);
        self.peek() == Some(kind)
    }

    pub(crate) fn at_ahead(&mut self, kind: TokenKind) -> bool {
        self.peek_ahead() == Some(kind)
    }

    fn at_set(&mut self, set: &[TokenKind]) -> bool {
        self.peek().map_or(false, |k| set.contains(&k))
    }

    pub(crate) fn at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    pub(crate) fn debug_kinds(&mut self) {
        self.source.debug_print();
    }

}
use std::fmt;

use itertools::Itertools;
use syntax::TokenKind;
use text_size::{TextRange, TextSize};

#[derive(PartialEq)]
pub struct Tokens {
    kinds: Vec<TokenKind>,
    starts: Vec<TextSize>,
}

impl Tokens {
    pub fn new(kinds: Vec<TokenKind>, starts: Vec<TextSize>) -> Self {
        debug_assert_eq!(kinds.len() + 1, starts.len());
        Self { kinds, starts }
    }

    pub fn kind(&self, idx: usize) -> TokenKind {
        self.kinds[idx]
    }

    pub fn get_kind(&self, idx: usize) -> Option<TokenKind> {
        self.kinds.get(idx).copied()
    }

    pub fn range(&self, idx: usize) -> TextRange {
        let start = self.starts[idx];
        let end = self.starts[idx + 1];
        TextRange::new(start, end)
    }

    pub fn iter(&self) -> impl Iterator<Item = (TokenKind, TextRange)> + '_ {
        self.kinds
            .iter()
            .copied()
            .zip_eq(self.starts.iter().copied())
            .zip_eq(self.starts.iter().copied().skip(1))
            .map(|((kind, start), end)| (kind, TextRange::new(start, end)))
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.kinds.len()
    }
}

impl fmt::Debug for Tokens {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (kind, range)) in self.iter().enumerate() {
            if i != 0 {
                writeln!(f)?;
            }

            write!(f, "{kind:?}@{range:?}")?;
        }

        Ok(())
    }
}

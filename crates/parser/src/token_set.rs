use syntax::TokenKind;

// Each bit represents whether that bit’s TokenKind is in the set.
//
// This is a TokenSet containing the first and third variants of TokenKind
// (regardless of what they may be):
//
//     0000000000000101
//
// Thus, the number of TokenKind variants must not exceed
// the number of bits in TokenSet.
//
// This implementation is mostly stolen from rust-analyzer:
// https://github.com/rust-analyzer/rust-analyzer/blob/b73b321478d3b2a98d380eb79de717e01620c4e9/crates/parser/src/token_set.rs
// (This implementation is also stolen lol)
#[derive(Debug, Clone, Copy)]
pub(crate) struct TokenSet(u64);

impl TokenSet {
    pub(crate) const ALL: Self = Self(u64::MAX);
    pub(crate) const NONE: Self = Self(0);

    pub(crate) const fn new<const LEN: usize>(kinds: [TokenKind; LEN]) -> Self {
        let mut value = 0;

        let mut idx = 0;
        while idx < kinds.len() {
            value |= mask(kinds[idx]);
            idx += 1;
        }

        Self(value)
    }
    
    pub(crate) const fn contains(self, kind: TokenKind) -> bool {
        self.0 & mask(kind) != 0
    }

    pub(crate) const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

const fn mask(kind: TokenKind) -> u64 {
    1 << kind as u64
}


#[cfg(test)]
#[test]
fn it_works() {
    let set = TokenSet::new([TokenKind::Arrow, TokenKind::Int]);

    assert!(set.contains(TokenKind::Arrow));
    assert!(set.contains(TokenKind::Int));
    assert!(!set.contains(TokenKind::StringContents));

    let set = set.union(TokenSet::new([TokenKind::StringContents]));

    assert!(set.contains(TokenKind::Arrow));
    assert!(set.contains(TokenKind::Int));
    assert!(set.contains(TokenKind::StringContents));
    assert!(!set.contains(TokenKind::Ident));
}

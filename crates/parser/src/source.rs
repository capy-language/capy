
use lexer::{Token, TokenKind};
use rowan::TextRange;

pub(crate) struct Source<'t, 'input> {
    tokens: &'t [Token<'input>],
    cursor: usize,
}

impl<'t, 'input> Source<'t, 'input> {
    pub(crate) fn new(tokens: &'t [Token<'input>]) -> Self {
        Self { tokens, cursor: 0 }
    }

    pub(crate) fn next_token(&mut self) -> Option<&'t Token<'input>> {
        self.eat_trivia();

        let token = self.tokens.get(self.cursor)?;
        self.cursor += 1;

        Some(token)
    }

    pub(crate) fn peek_kind(&mut self, offset: usize) -> Option<TokenKind> {
        self.peek_token(offset).map(|Token { kind, .. }| *kind)
    }

    pub(crate) fn peek_token(&mut self, offset: usize) -> Option<&Token> {
        let c = self.cursor;
        self.eat_trivia();
        for _ in 0..offset {
            self.cursor += 1;
            self.eat_trivia();
        }
        let res = self.tokens.get(self.cursor);
        self.cursor = c;
        res
    }

    pub(crate) fn last_token_range(&self) -> Option<TextRange> {
        self.tokens.last().map(|Token { range, .. }| *range)
    }

    fn eat_trivia(&mut self) {
        while self.at_trivia() {
            self.cursor += 1;
        }
    }

    fn at_trivia(&self) -> bool {
        self.peek_kind_raw().map_or(false, TokenKind::is_trivia)
    }

    pub(crate) fn peek_token_raw(&self) -> Option<&Token> {
        self.tokens.get(self.cursor)
    }

    pub(crate) fn peek_kind_raw(&self) -> Option<TokenKind> {
        self.peek_token_raw().map(|Token { kind, .. }| *kind)
    }

    pub(crate) fn debug_print(&self) {
        for (idx, Token { kind, text, ..}) in self.tokens.iter().enumerate() {
            println!("   {:#?} {:#?} {}", kind, text, if self.cursor == idx { "<-" } else { "" });
        }
        println!();
    }
}

#[cfg(test)]
mod tests {
    use lexer::Lexer;
    use super::*;

    #[test]
    fn peek() {
        let tokens: Vec<_> = Lexer::new("1a+").collect();
        let mut source = Source::new(&tokens);
        let peek = source.peek_kind(0);
        assert_eq!(
            peek,
            Some(TokenKind::Number)
        )
    }

    #[test]
    fn peek_ahead_once() {
        let tokens: Vec<_> = Lexer::new("1a+").collect();
        let mut source = Source::new(&tokens);
        let peek = source.peek_kind(1);
        assert_eq!(
            peek,
            Some(TokenKind::Ident)
        )
    }

    #[test]
    fn peek_ahead_twice() {
        let tokens: Vec<_> = Lexer::new("1a+2b").collect();
        let mut source = Source::new(&tokens);
        let peek = source.peek_kind(2);
        assert_eq!(
            peek,
            Some(TokenKind::Plus)
        )
    }
}
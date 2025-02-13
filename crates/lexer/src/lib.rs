use std::mem;

use logos::Logos;
use syntax::TokenKind;
use token::Tokens;

use text_size::TextSize;

pub fn lex(text: &str) -> Tokens {
    let mut kinds = Vec::new();
    let mut starts = Vec::new();

    let mut lexer = LexerTokenKind::lexer(text);
    while let Some(kind) = lexer.next() {
        let range = lexer.span();
        let start = (range.start as u32).into();

        let mut handler = |k, s| {
            kinds.push(k);
            starts.push(s);
        };

        match kind {
            Ok(LexerTokenKind::__InternalChar) => lex_char(lexer.slice(), start, handler),
            Ok(LexerTokenKind::__InternalString) => lex_string(lexer.slice(), start, handler),
            Ok(LexerTokenKind::__InternalComment) => lex_comment(start, range.len(), handler),
            Ok(kind) => {
                let transmuted = unsafe { mem::transmute::<LexerTokenKind, TokenKind>(kind) };
                // we compare the debug names of the two values to ensure that no transmutation bugs occurred
                debug_assert_eq!(format!("{:?}", kind), format!("{:?}", transmuted));
                handler(transmuted, start)
            }
            // todo: make sure this actually works as it did before
            Err(_) => handler(TokenKind::Error, start),
        }
    }

    starts.push((text.len() as u32).into());

    kinds.shrink_to_fit();
    starts.shrink_to_fit();

    Tokens::new(kinds, starts)
}

fn lex_char(s: &str, offset: TextSize, mut f: impl FnMut(TokenKind, TextSize)) {
    #[derive(Clone, Copy)]
    enum Mode {
        StartContents,
        InContents,
        Escape,
    }

    let mut mode = Mode::InContents;
    let mut pos = offset;

    for c in s.chars() {
        match (mode, c) {
            (Mode::InContents | Mode::StartContents, '\'') => {
                mode = Mode::StartContents;
                f(TokenKind::SingleQuote, pos);
            }
            (Mode::InContents | Mode::StartContents, '\\') => {
                mode = Mode::Escape;
                f(TokenKind::Escape, pos);
            }
            (Mode::StartContents, _) => {
                mode = Mode::InContents;
                f(TokenKind::StringContents, pos);
            }
            (Mode::InContents, _) => {}
            (Mode::Escape, _) => mode = Mode::StartContents,
        }

        pos += TextSize::from(c.len_utf8() as u32);
    }
}

fn lex_string(s: &str, offset: TextSize, mut f: impl FnMut(TokenKind, TextSize)) {
    #[derive(Clone, Copy)]
    enum Mode {
        StartContents,
        InContents,
        Escape,
    }

    let mut mode = Mode::InContents;
    let mut pos = offset;

    for c in s.chars() {
        match (mode, c) {
            (Mode::InContents | Mode::StartContents, '"') => {
                mode = Mode::StartContents;
                f(TokenKind::DoubleQuote, pos);
            }
            (Mode::InContents | Mode::StartContents, '\\') => {
                mode = Mode::Escape;
                f(TokenKind::Escape, pos);
            }
            (Mode::StartContents, _) => {
                mode = Mode::InContents;
                f(TokenKind::StringContents, pos);
            }
            (Mode::InContents, _) => {}
            (Mode::Escape, _) => mode = Mode::StartContents,
        }

        pos += TextSize::from(c.len_utf8() as u32);
    }
}

fn lex_comment(offset: TextSize, len: usize, mut f: impl FnMut(TokenKind, TextSize)) {
    f(TokenKind::CommentLeader, offset);

    if len > 1 {
        f(TokenKind::CommentContents, offset + TextSize::from(2));
    }
}

capy_macros::define_token_enum! {
    LexerTokenKind, full, "../../tokenizer.txt"
}

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
            LexerTokenKind::__InternalString => lex_string(lexer.slice(), start, handler),
            LexerTokenKind::__InternalComment => lex_comment(start, range.len(), handler),
            _ => handler(unsafe { mem::transmute(kind) }, start),
        }
    }

    starts.push((text.len() as u32).into());

    kinds.shrink_to_fit();
    starts.shrink_to_fit();

    Tokens::new(kinds, starts)
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
                f(TokenKind::Quote, pos);
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

// ! This enum must match up exactly with the contents of syntax::TokenKind
// ! The source of a really horrible bug
#[derive(Debug, Copy, Clone, PartialEq, Logos)]
pub enum LexerTokenKind {
    #[regex("[ \r\n]+")]
    Whitespace,

    #[token("mut")]
    Mut,

    #[token("as")]
    As,

    #[token("if")]
    If,

    #[token("else")]
    Else,

    #[token("while")]
    While,

    #[token("loop")]
    Loop,

    #[regex("[A-Za-z_][A-Za-z0-9_]*")]
    Ident,

    #[regex("[0-9]+")]
    Int,

    #[regex("true|false")]
    Bool,

    _Quote,

    _Escape,

    _StringContents,

    #[token("+")]
    Plus,

    #[token("-")]
    Hyphen,

    #[token("*")]
    Asterisk,

    #[token("/")]
    Slash,

    #[token("<")]
    Less,

    #[token("<=")]
    LessEquals,

    #[token(">")]
    Greater,

    #[token(">=")]
    GreaterEquals,

    #[token("!")]
    Bang,

    #[token("!=")]
    BangEquals,

    #[token("&&")]
    DoubleAnd,

    #[token("||")]
    DoublePipe,

    #[token("==")]
    DoubleEquals,

    #[token("=")]
    Equals,

    #[token(",")]
    Comma,

    #[token(".")]
    Dot,

    #[token("->")]
    Arrow,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("[")]
    LBrack,

    #[token("]")]
    RBrack,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    _CommentLeader,

    _CommentContents,

    #[token(":")]
    Colon,

    #[token(";")]
    Semicolon,

    #[error]
    Error,

    // These are internal and so don't have to have
    // representation in syntax::TokenKind
    #[regex(r#""([^"\\\n]|\\.)*"?"#)]
    __InternalString,

    #[regex("//.*")]
    __InternalComment,
}

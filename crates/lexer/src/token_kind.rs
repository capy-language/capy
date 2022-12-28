use std::fmt;

use logos::Logos;

#[derive(Debug, Copy, Clone, PartialEq, Logos)]
pub enum TokenKind {
    #[error]
    Error,

    #[regex("[ \r\n]+")]
    Whitespace,

    #[regex("[A-Za-z_][A-Za-z0-9_]*")]
    Ident,

    #[regex("[0-9]+")]
    Number,

    #[token("+")]
    Plus,

    #[token("-")]
    Hyphen,

    #[token("*")]
    Asterisk,

    #[token("/")]
    Slash,

    #[token("=")]
    Equals,

    #[token("->")]
    Arrow,

    #[token(".")]
    Dot,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[regex("//.*")]
    Comment,

    #[token(";")]
    Semicolon,

    #[regex(r#""([^"\\\n]|\\.)*"?"#)]
    String,
}

impl TokenKind {
    pub fn is_trivia(self) -> bool {
        matches!(self, Self::Whitespace | Self::Comment)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Whitespace => "whitespace",
            Self::Ident => "identifier",
            Self::Number => "number",
            Self::Plus => "'+'",
            Self::Hyphen => "'-'",
            Self::Asterisk => "'*'",
            Self::Slash => "'/'",
            Self::Equals => "'='",
            Self::Dot => ".",
            Self::Arrow => "->",
            Self::LParen => "'('",
            Self::RParen => "')'",
            Self::LBrace => "'{'",
            Self::RBrace => "'}'",
            Self::Semicolon => "';'",
            Self::Comment => "comment",
            Self::Error => "an unrecognized token",
            Self::String => "string",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Lexer;
    
    fn check(input: &str, kind: TokenKind) {
        let mut lexer = Lexer::new(input);

        let token = lexer.next().unwrap();
        assert_eq!(token.kind, kind);
        assert_eq!(token.text, input);
    }

    #[test]
    fn lex_spaces() {
        check("   ", TokenKind::Whitespace);
    }

    #[test]
    fn lex_spaces_and_newlines() {
        check("  \n ", TokenKind::Whitespace);
    }

    #[test]
    fn lex_single_char_identifier() {
        check("x", TokenKind::Ident);
    }

    #[test]
    fn lex_alphabetic_identifier() {
        check("abcd", TokenKind::Ident);
    }

    #[test]
    fn lex_alphanumeric_identifier() {
        check("ab123cde456", TokenKind::Ident);
    }

    #[test]
    fn lex_mixed_case_identifier() {
        check("ABCdef", TokenKind::Ident);
    }

    #[test]
    fn lex_number() {
        check("123456", TokenKind::Number);
    }

    #[test]
    fn lex_plus() {
        check("+", TokenKind::Plus);
    }

    #[test]
    fn lex_minus() {
        check("-", TokenKind::Hyphen);
    }

    #[test]
    fn lex_star() {
        check("*", TokenKind::Asterisk);
    }

    #[test]
    fn lex_slash() {
        check("/", TokenKind::Slash);
    }

    #[test]
    fn lex_equals() {
        check("=", TokenKind::Equals);
    }

    #[test]
    fn lex_dot() {
        check(".", TokenKind::Dot);
    }

    #[test]
    fn lex_arrow() {
        check("->", TokenKind::Arrow);
    } 

    #[test]
    fn lex_left_brace() {
        check("{", TokenKind::LBrace);
    }

    #[test]
    fn lex_right_brace() {
        check("}", TokenKind::RBrace);
    }

    #[test]
    fn lex_left_paren() {
        check("(", TokenKind::LParen);
    }

    #[test]
    fn lex_right_paren() {
        check(")", TokenKind::RParen);
    }

    #[test]
    fn lex_comment() {
        check("// foo", TokenKind::Comment);
    }

    #[test]
    fn lex_semicolon() {
        check(";", TokenKind::Semicolon);
    }

    #[test]
    fn lex_string() {
        check(r#""Hello, World!""#, TokenKind::String);
    }
}

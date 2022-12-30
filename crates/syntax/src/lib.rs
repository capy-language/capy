
use lexer::TokenKind;
use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::{FromPrimitive, ToPrimitive};

#[derive(Debug, Copy, Clone, PartialEq, FromPrimitive, ToPrimitive)]
pub enum SyntaxKind {
    Whitespace,
    Ident,
    Number,
    StringContents,
    Plus,
    Hyphen,
    Asterisk,
    Slash,
    Equals,
    Comma,
    Arrow,
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comment,
    Error,
    Root,
    InfixExpr,
    IntLiteral,
    StringLiteral,
    ParenExpr,
    BlockExpr,
    Params,
    LambdaExpr,
    PrefixExpr,
    Return,
    VariableDef,
    VariableRef,
    VariableCall,
    Semicolon,
}

impl From<TokenKind> for SyntaxKind {
    fn from(token_kind: TokenKind) -> Self {
        match token_kind {
            TokenKind::Whitespace => Self::Whitespace,
            TokenKind::Ident => Self::Ident,
            TokenKind::Number => Self::Number,
            TokenKind::Plus => Self::Plus,
            TokenKind::Hyphen => Self::Hyphen,
            TokenKind::Asterisk => Self::Asterisk,
            TokenKind::Slash => Self::Slash,
            TokenKind::Equals => Self::Equals,
            TokenKind::Dot => unimplemented!(),
            TokenKind::Comma => Self::Comma,
            TokenKind::Arrow => Self::Arrow,
            TokenKind::LParen => Self::LParen,
            TokenKind::RParen => Self::RParen,
            TokenKind::LBrace => Self::LBrace,
            TokenKind::RBrace => Self::RBrace,
            TokenKind::Comment => Self::Comment,
            TokenKind::Error => Self::Error,
            TokenKind::Semicolon => Self::Semicolon,
            TokenKind::String => Self::StringContents,
            TokenKind::Return => Self::Return,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum CapyLanguage {}

impl rowan::Language for CapyLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        Self::Kind::from_u16(raw.0).unwrap()
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.to_u16().unwrap())
    }
}

pub type SyntaxNode = rowan::SyntaxNode<CapyLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<CapyLanguage>;
pub type SyntaxElement = rowan::SyntaxElement<CapyLanguage>;

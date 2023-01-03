use std::fmt;

use syntax::TokenKind;
use text_size::{TextSize, TextRange};

#[derive(Clone, Copy, PartialEq)]
pub struct SyntaxError {
    pub expected_syntax: ExpectedSyntax,
    pub kind: SyntaxErrorKind,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SyntaxErrorKind {
    Missing { 
        offset: TextSize 
    },
    Unexpected { 
        found: TokenKind,
        range: TextRange,
    },
}

impl fmt::Debug for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error at ")?;
        match self.kind {
            SyntaxErrorKind::Missing { offset } => write!(f, "{}", u32::from(offset))?,
            SyntaxErrorKind::Unexpected { range, .. } => {
                write!(f, "{}..{}", u32::from(range.start()), u32::from(range.end()))?;
            },
        }
        write!(f, ": ")?;

        let format_expected_syntax = |f: &mut fmt::Formatter<'_>| match self.expected_syntax {
            ExpectedSyntax::Named(name) => write!(f, "{}", name),
            ExpectedSyntax::Unnamed(kind) => write!(f, "{:?}", kind),
        };

        match self.kind {
            SyntaxErrorKind::Missing { .. } => {
                write!(f, "missing ")?;
                format_expected_syntax(f);
            },
            SyntaxErrorKind::Unexpected { found, .. } => {
                write!(f, "expected ")?;
                format_expected_syntax(f);
                write!(f, " but found {:?}", found)?;
            },
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExpectedSyntax {
    Named(&'static str),
    Unnamed(TokenKind),
}

#[cfg(test)]
mod tests {
    // use super::*;
    // use std::ops::Range as StdRange;
    //
    // fn check(
    //     expected_syntax: ExpectedSyntax,
    //     found: Option<LexerTokenKind>,
    //     range: StdRange<u32>,
    //     output: &str,
    // ) {
    //     let error: SyntaxError = if let Some(found) = found {
    //         SyntaxError {
    //             expected_syntax,
    //             kind: SyntaxErrorKind::Unexpected { 
    //                 found, 
    //                 range: {
    //                     let start = range.start.into();
    //                     let end = range.end.into();
    //                     TextRange::new(start, end)
    //                 } 
    //             }
    //         }
    //     } else {
    //         SyntaxError {
    //             expected_syntax,
    //             kind: SyntaxErrorKind::Missing { 
    //                 offset: range.start.into()
    //             }
    //         }
    //     };

    //     assert_eq!(format!("{:?}", error), output);
    // }

    // #[test]
    // fn one_expected_did_find() {
    //     check(
    //         vec![LexerTokenKind::Equals],
    //         Some(LexerTokenKind::Ident),
    //         10..20,
    //         "error at 10..20: expected '=' but found identifier",
    //     );
    // }

    // #[test]
    // fn one_expected_did_not_find() {
    //     check(
    //         vec![LexerTokenKind::RParen],
    //         None,
    //         5..6,
    //         "error at 5: missing ')'",
    //     );
    // }

    // #[test]
    // fn multiple_expected_did_find() {
    //     check(
    //         vec![
    //             LexerTokenKind::Number,
    //             LexerTokenKind::Ident,
    //             LexerTokenKind::Hyphen,
    //             LexerTokenKind::LParen,
    //         ],
    //         Some(LexerTokenKind::Semicolon),
    //         100..105,
    //         "error at 100..105: expected number, identifier, '-' or '(' but found ';'",
    //     );
    // }
    
    // #[test]
    // fn two_expected_did_find() {
    //     check(
    //         vec![LexerTokenKind::Plus, LexerTokenKind::Hyphen],
    //         Some(LexerTokenKind::Equals),
    //         0..1,
    //         "error at 0..1: expected '+' or '-' but found '='",
    //     );
    // }
}

use std::vec;

use ast::validation::{ValidationDiagnostic, ValidationDiagnosticKind};
use hir::{IndexingDiagnostic, IndexingDiagnosticKind, LoweringDiagnostic, LoweringDiagnosticKind};
use hir_types::TypeDiagnostic;
use interner::Interner;
use line_index::{LineIndex, LineNr, ColNr};
use parser::{SyntaxError, SyntaxErrorKind, ExpectedSyntax};
use syntax::TokenKind;
use text_size::{TextRange, TextSize};


pub struct Diagnostic(Repr);

enum Repr {
    Syntax(SyntaxError),
    Validation(ValidationDiagnostic),
    Indexing(IndexingDiagnostic),
    Lowering(LoweringDiagnostic),
    Type(TypeDiagnostic),
}

pub enum Severity {
    Warning,
    Error,
}

impl Diagnostic {
    pub fn from_syntax(error: SyntaxError) -> Self {
        Self(Repr::Syntax(error))
    }

    pub fn from_validation(diagnostic: ValidationDiagnostic) -> Self {
        Self(Repr::Validation(diagnostic))
    }

    pub fn from_indexing(diagnostic: IndexingDiagnostic) -> Self {
        Self(Repr::Indexing(diagnostic))
    }

    pub fn from_lowering(diagnostic: LoweringDiagnostic) -> Self {
        Self(Repr::Lowering(diagnostic))
    }

    pub fn from_type(diagnostic: TypeDiagnostic) -> Self {
        Self(Repr::Type(diagnostic))
    }

    pub fn display(&self, input: &str, interner: &Interner, line_index: &LineIndex) -> Vec<String> {
        let range = self.range();

        let (start_line, start_col) = line_index.line_col(range.start());

        // we subtract 1 since end_line_column is inclusive,
        // unlike TextRange which is always exclusive
        let (end_line, end_col) = line_index.line_col(range.end() - TextSize::from(1));

        const ANSI_YELLOW: &str = "\x1B[1;93m";
        const ANSI_RED: &str = "\x1B[1;91m";
        const ANSI_WHITE: &str = "\x1B[1;97m";

        let severity = match self.severity() {
            Severity::Warning => format!("{}warning", ANSI_YELLOW),
            Severity::Error => format!("{}error", ANSI_RED),
        };

        let mut lines = vec![format!(
            "{}{}: {}",
            severity,
            ANSI_WHITE,
            self.message(interner)
        )];

        input_snippet(input, start_line, start_col, end_line, end_col, range, &mut lines);

        lines
    }

    pub fn range(&self) -> TextRange {
        match self.0 {
            Repr::Syntax(SyntaxError { kind: SyntaxErrorKind::Missing { offset }, .. }) => {
                TextRange::new(offset, offset + TextSize::from(1))
            },
            Repr::Syntax(SyntaxError { 
                kind: SyntaxErrorKind::Unexpected { range, .. }, .. 
            }) => range,
            Repr::Validation(ValidationDiagnostic { range, .. }) => range,
            Repr::Indexing(IndexingDiagnostic { range, .. }) => range,
            Repr::Lowering(LoweringDiagnostic { range, .. }) => range,
            Repr::Type(TypeDiagnostic { range, .. }) => range,
        }
    }

    pub fn severity(&self) -> Severity {
        match &self.0 {
            Repr::Syntax(_) => Severity::Error,
            Repr::Validation(_) => Severity::Warning,
            Repr::Indexing(_) => Severity::Error,
            Repr::Lowering(_) => Severity::Error,
            Repr::Type(_) => Severity::Error,
        }
    }

    pub fn message(&self, interner: &Interner) -> String {
        match &self.0 {
            Repr::Syntax(e) => syntax_error_message(e),
            Repr::Validation(d) => validation_diagnostic_message(d),
            Repr::Indexing(d) => indexing_diagnostic_message(d, interner),
            Repr::Lowering(d) => lowering_diagnostic_message(d, interner),
            Repr::Type(d) => type_diagnostic_message(d, interner),
        }
    }
}

fn input_snippet(
    input: &str,
    start_line: LineNr,
    start_col: ColNr,
    end_line: LineNr,
    end_col: ColNr,
    range: TextRange,
    lines: &mut Vec<String>,
) {
    const ANSI_RESET: &str = "\x1B[0m";
    const ANSI_GRAY: &str = "\x1B[1;90m";
    const ANSI_YELLOW: &str = "\x1B[1;93m";

    const PADDING: &str = " | ";
    const POINTER_UP: &str = "^";
    const POINTER_DOWN: &str = "v";

    let file_lines: Vec<_> = input.lines().collect();

    let is_single_line = start_line == end_line;
    if is_single_line {
        let line_number_padding = " ".repeat(count_digits(start_line.0 + 1, 10));
        
        lines.push(format!(
            "{}{}--> at {}:{}",
            ANSI_GRAY,
            line_number_padding,
            start_line.0 + 1,
            start_col.0 + 1,
        ));

        lines.push(format!(
            "{}{}{}",
            ANSI_GRAY,
            line_number_padding,
            PADDING
        ));

        lines.push(format!(
            "{}{}{}{}{}",
            ANSI_GRAY,
            start_line.0 + 1,
            PADDING, 
            ANSI_RESET,
            file_lines[start_line.0 as usize]
        ));

        lines.push(format!(
            "{}{}{}{}{}{}{}",
            ANSI_GRAY,
            line_number_padding,
            PADDING,
            " ".repeat(start_col.0 as usize),
            ANSI_YELLOW,
            POINTER_UP.repeat(range.len().try_into().unwrap()),
            ANSI_RESET
        ));

        return;
    }

    let line_number_padding = " ".repeat(count_digits(end_line.0 + 1, 10));

    lines.push(format!(
        "{}{}--> at {}:{}",
        ANSI_GRAY,
        line_number_padding,
        start_line.0 + 1,
        start_col.0 + 1,
    ));

    lines.push(format!(
        "{}{}{}",
        ANSI_GRAY,
        line_number_padding,
        PADDING
    ));

    let first_line = file_lines[start_line.0 as usize];
    lines.push(format!(
        "{}{}{}{}{}{}",
        ANSI_GRAY,
        line_number_padding,
        PADDING,
        " ".repeat(start_col.0 as usize),
        ANSI_YELLOW,
        POINTER_DOWN.repeat(first_line.len() - start_col.0 as usize)
    ));
    lines.push(format!(
        "{}{}{}{}{}{}", 
        ANSI_GRAY,
        PADDING,
        start_line.0 + 1,
        " ".repeat(count_digits(end_line.0 + 1, 10) - count_digits(start_line.0 + 1, 10)),
        ANSI_RESET,
        first_line));

    for line in &file_lines[start_line.0 as usize + 1..end_line.0 as usize] {
        lines.push(format!(
            "{}{}{}{}{}", 
            ANSI_GRAY,
            PADDING,
            line_number_padding,
            ANSI_RESET,
            line));
    }

    let last_line = file_lines[end_line.0 as usize];
    lines.push(format!(
        "{}{}{}{}{}", 
        ANSI_GRAY,
        PADDING,
        end_line.0 + 1,
        ANSI_RESET,
        last_line));
    lines.push(format!(
        "{}{}{}{}{}{}", 
        ANSI_GRAY,
        PADDING,
        line_number_padding,
        ANSI_YELLOW,
        POINTER_UP.repeat(end_col.0 as usize + 1),
        ANSI_RESET));
}

// count the digits in a number e.g.
// 42 => 2
fn count_digits(n: u32, base: u32) -> usize {
    let mut power = base;
    let mut count = 1;
    while n >= power {
        count += 1;
        if let Some(new_power) = power.checked_mul(base) {
            power = new_power;
        } else {
            break;
        }
    }
    count
}

fn syntax_error_message(e: &SyntaxError) -> String {
    let write_expected_syntax = |buf: &mut String| match e.expected_syntax {
        ExpectedSyntax::Named(name) => buf.push_str(&format!("{}", name)),
        ExpectedSyntax::Unnamed(kind) => buf.push_str(&format!("{}", format_kind(kind))),
    };

    let mut message = String::new();

    match e.kind {
        SyntaxErrorKind::Missing { .. } => {
            message.push_str("missing ");
            write_expected_syntax(&mut message);
        }
        SyntaxErrorKind::Unexpected { found, .. } => {
            message.push_str("expected ");
            write_expected_syntax(&mut message);
            message.push_str(&format!(" but found {}", format_kind(found)));
        }
    }

    message
}

fn validation_diagnostic_message(d: &ValidationDiagnostic) -> String {
    match d.kind {
        ValidationDiagnosticKind::UnneededVoid => "unneeded `void`".to_string(),
    }
}

fn indexing_diagnostic_message(d: &IndexingDiagnostic, interner: &Interner) -> String {
    match &d.kind {
        IndexingDiagnosticKind::AlreadyDefined { name } => {
            format!("name `{}` already defined", interner.lookup(*name))
        }
    }
}

fn lowering_diagnostic_message(d: &LoweringDiagnostic, interner: &Interner) -> String {
    match &d.kind {
        LoweringDiagnosticKind::OutOfRangeIntLiteral => "integer literal out of range".to_string(),
        LoweringDiagnosticKind::UndefinedLocal { name } => {
            format!("undefined variable `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::UndefinedModule { name } => {
            format!("undefined module `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::MismatchedArgCount { name, expected, got } => {
            format!("`{}` expected {} arguments, but got {}", interner.lookup(*name), expected, got)
        }
        LoweringDiagnosticKind::CalledNonLambda { name } => {
            format!(
                "tried to call `{}`, which is not a lambda",
                interner.lookup(*name)
            )
        }
        LoweringDiagnosticKind::InvalidEscape => "invalid escape".to_string(),
    }
}

fn type_diagnostic_message(d: &TypeDiagnostic, interner: &Interner) -> String {
    match &d.kind {
        hir_types::TypeDiagnosticKind::Mismatch { expected, found } => {
            format!(
                "expected `{}` but found `{}`",
                expected.display(interner),
                found.display(interner),
            )
        },
        hir_types::TypeDiagnosticKind::Undefined { name } => {
            format!("undefined type `{}`", interner.lookup(*name))
        },
    }
}

fn format_kind(kind: TokenKind) -> &'static str {
    match kind {
        TokenKind::Ident => "identifier",
        TokenKind::Int => "integer literal",
        TokenKind::Quote => "`\"`",
        TokenKind::Escape => "escape sequence",
        TokenKind::StringContents => "string literal",
        TokenKind::Plus => "`+`",
        TokenKind::Hyphen => "`-`",
        TokenKind::Asterisk => "`*`",
        TokenKind::Slash => "`/`",
        TokenKind::Equals => "`=`",
        TokenKind::Dot => "`.`",
        TokenKind::Colon => "`:`",
        TokenKind::Comma => "`,`",
        TokenKind::Semicolon => "`;`",
        TokenKind::Arrow => "`->`",
        TokenKind::LParen => "`(`",
        TokenKind::RParen => "`)`",
        TokenKind::LBrace => "`{`",
        TokenKind::RBrace => "`}`",
        TokenKind::Whitespace => "whitespace",
        TokenKind::CommentContents | TokenKind::CommentLeader => "comment",
        TokenKind::Error => "an unrecognized token",
    }
}
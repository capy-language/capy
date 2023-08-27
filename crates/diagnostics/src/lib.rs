use std::vec;

use ast::validation::{ValidationDiagnostic, ValidationDiagnosticKind};
use hir::{
    IndexingDiagnostic, IndexingDiagnosticKind, LoweringDiagnostic, LoweringDiagnosticKind,
    TyParseError,
};
use hir_ty::{ResolvedTy, TyDiagnostic, TyDiagnosticHelp};
use interner::Interner;
use la_arena::Arena;
use line_index::{ColNr, LineIndex, LineNr};
use parser::{ExpectedSyntax, SyntaxError, SyntaxErrorKind};
use syntax::TokenKind;
use text_size::{TextRange, TextSize};

pub struct Diagnostic(Repr);

enum Repr {
    Syntax(SyntaxError),
    Validation(ValidationDiagnostic),
    Indexing(IndexingDiagnostic),
    Lowering(LoweringDiagnostic),
    Ty(TyDiagnostic),
}

#[derive(PartialEq)]
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

    pub fn from_ty(diagnostic: TyDiagnostic) -> Self {
        Self(Repr::Ty(diagnostic))
    }

    pub fn display(
        &self,
        filename: &str,
        input: &str,
        resolved_arena: &Arena<ResolvedTy>,
        interner: &Interner,
        line_index: &LineIndex,
    ) -> Vec<String> {
        let range = self.range();

        let (start_line, start_col) = line_index.line_col(range.start());

        // we subtract 1 since end_line_column is inclusive,
        // unlike TextRange which is always exclusive
        let (end_line, end_col) = line_index.line_col(range.end() - TextSize::from(1));

        const ANSI_YELLOW: &str = "\x1B[1;93m";
        const ANSI_RED: &str = "\x1B[1;91m";
        const ANSI_WHITE: &str = "\x1B[1;97m";
        const ANSI_CYAN: &str = "\x1B[1;96m";

        let severity = match self.severity() {
            Severity::Warning => format!("{}warning", ANSI_YELLOW),
            Severity::Error => format!("{}error", ANSI_RED),
        };

        let mut lines = vec![format!(
            "{}{}: {}",
            severity,
            ANSI_WHITE,
            self.message(resolved_arena, interner)
        )];

        input_snippet(
            filename, input, start_line, start_col, end_line, end_col, range, &mut lines,
        );

        if let Some(help) = self.help() {
            lines.push(format!(
                "{}help{}: {}",
                ANSI_CYAN,
                ANSI_WHITE,
                help.message()
            ));

            let range = help.range();

            let (start_line, start_col) = line_index.line_col(range.start());

            // we subtract 1 since end_line_column is inclusive,
            // unlike TextRange which is always exclusive
            let (end_line, end_col) = line_index.line_col(range.end() - TextSize::from(1));

            input_snippet(
                filename, input, start_line, start_col, end_line, end_col, range, &mut lines,
            );
        }

        lines
    }

    pub fn range(&self) -> TextRange {
        match self.0 {
            Repr::Syntax(SyntaxError {
                kind: SyntaxErrorKind::Missing { offset },
                ..
            }) => TextRange::new(offset, offset + TextSize::from(1)),
            Repr::Syntax(SyntaxError {
                kind: SyntaxErrorKind::Unexpected { range, .. },
                ..
            }) => range,
            Repr::Validation(ValidationDiagnostic { range, .. }) => range,
            Repr::Indexing(IndexingDiagnostic { range, .. }) => range,
            Repr::Lowering(LoweringDiagnostic { range, .. }) => range,
            Repr::Ty(TyDiagnostic { range, .. }) => range,
        }
    }

    pub fn severity(&self) -> Severity {
        match &self.0 {
            Repr::Syntax(_) => Severity::Error,
            Repr::Validation(_) => Severity::Warning,
            Repr::Indexing(_) => Severity::Error,
            Repr::Lowering(_) => Severity::Error,
            Repr::Ty(_) => Severity::Error,
        }
    }

    pub fn message(&self, resolved_arena: &Arena<ResolvedTy>, interner: &Interner) -> String {
        match &self.0 {
            Repr::Syntax(e) => syntax_error_message(e),
            Repr::Validation(d) => validation_diagnostic_message(d),
            Repr::Indexing(d) => indexing_diagnostic_message(d, interner),
            Repr::Lowering(d) => lowering_diagnostic_message(d, interner),
            Repr::Ty(d) => ty_diagnostic_message(d, resolved_arena, interner),
        }
    }

    pub fn help(&self) -> Option<HelpDiagnostic> {
        match &self.0 {
            Repr::Syntax(SyntaxError { .. }) => None,
            Repr::Validation(ValidationDiagnostic { .. }) => None,
            Repr::Indexing(IndexingDiagnostic { .. }) => None,
            Repr::Lowering(LoweringDiagnostic { .. }) => None,
            Repr::Ty(TyDiagnostic { help, .. }) => help.as_ref().map(HelpDiagnostic::Ty),
        }
    }
}

pub enum HelpDiagnostic<'a> {
    Ty(&'a TyDiagnosticHelp),
}

impl HelpDiagnostic<'_> {
    pub fn range(&self) -> TextRange {
        match self {
            HelpDiagnostic::Ty(d) => d.range,
        }
    }

    pub fn message(&self) -> String {
        match &self {
            HelpDiagnostic::Ty(d) => ty_diagnostic_help_message(d),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn input_snippet(
    filename: &str,
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
    // const POINTER_DOWN: &str = "v";

    let file_lines: Vec<_> = input.lines().collect();

    let is_single_line = start_line == end_line;
    if is_single_line {
        let line_number_padding = " ".repeat(count_digits(start_line.0 + 1, 10));

        lines.push(format!(
            "{}{}--> at {}:{}:{}",
            ANSI_GRAY,
            line_number_padding,
            filename,
            start_line.0 + 1,
            start_col.0 + 1,
        ));

        lines.push(format!("{}{}{}", ANSI_GRAY, line_number_padding, PADDING));

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

    // multi-line errors:

    let line_number_padding = " ".repeat(count_digits(end_line.0 + 1, 10));

    lines.push(format!(
        "{}{}--> at {}:{}:{}",
        ANSI_GRAY,
        line_number_padding,
        filename,
        start_line.0 + 1,
        start_col.0 + 1,
    ));

    // blank line
    lines.push(format!("{}{}{}", ANSI_GRAY, line_number_padding, PADDING));

    // now start printing the actual lines of code
    let first_line = file_lines[start_line.0 as usize];
    lines.push(format!(
        "{}{}{}{}{}{}{}{}",
        ANSI_GRAY,
        start_line.0 + 1,
        " ".repeat(count_digits(end_line.0 + 1, 10) - count_digits(start_line.0 + 1, 10)),
        PADDING,
        ANSI_YELLOW,
        "  ",
        ANSI_RESET,
        first_line
    ));

    // arrow below first line
    lines.push(format!(
        "{}{}{}{}{}{}{}",
        ANSI_GRAY,
        line_number_padding,
        PADDING,
        ANSI_YELLOW,
        " ",
        "_".repeat(start_col.0 as usize + 1),
        POINTER_UP,
        //"-".repeat(first_line.len() - start_col.0 as usize + 2)
    ));

    for (num, file_line) in file_lines
        .iter()
        .enumerate()
        .take(start_line.0 as usize + 1)
        .skip(end_line.0 as usize)
    {
        lines.push(format!(
            "{}{}{}{}{}{}{}{}",
            ANSI_GRAY,
            num + 1,
            " ".repeat(count_digits(end_line.0 + 1, 10) - count_digits(num as u32 + 1, 10)),
            PADDING,
            ANSI_YELLOW,
            "| ",
            ANSI_RESET,
            file_line
        ));
    }

    let last_line = file_lines[end_line.0 as usize];
    lines.push(format!(
        "{}{}{}{}{}{}{}",
        ANSI_GRAY,
        end_line.0 + 1,
        PADDING,
        ANSI_YELLOW,
        "| ",
        ANSI_RESET,
        last_line
    ));
    lines.push(format!(
        "{}{}{}{}{}{}{}{}",
        ANSI_GRAY,
        line_number_padding,
        PADDING,
        ANSI_YELLOW,
        "|",
        "_".repeat(end_col.0 as usize + 1),
        POINTER_UP,
        ANSI_RESET
    ));
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
        ExpectedSyntax::Named(name) => buf.push_str(name),
        ExpectedSyntax::Unnamed(kind) => buf.push_str(format_kind(kind)),
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
        ValidationDiagnosticKind::AlwaysTrue => "this is always true".to_string(),
        ValidationDiagnosticKind::AlwaysFalse => "this is always false".to_string(),
    }
}

fn indexing_diagnostic_message(d: &IndexingDiagnostic, interner: &Interner) -> String {
    match &d.kind {
        IndexingDiagnosticKind::NonBindingAtRoot => {
            "all globals must be binding `::` and not variable `:=`".to_string()
        }
        IndexingDiagnosticKind::AlreadyDefined { name } => {
            format!("name `{}` already defined", interner.lookup(*name))
        }
        IndexingDiagnosticKind::MissingTy { name } => {
            format!("global `{}` must have a type", interner.lookup(*name))
        }
        IndexingDiagnosticKind::TyParseError(parse_error) => lower_ty_parse_error(parse_error),
    }
}

fn lowering_diagnostic_message(d: &LoweringDiagnostic, interner: &Interner) -> String {
    match &d.kind {
        LoweringDiagnosticKind::OutOfRangeIntLiteral => "integer literal out of range".to_string(),
        LoweringDiagnosticKind::OutOfRangeFloatLiteral => "float literal out of range".to_string(),
        LoweringDiagnosticKind::UndefinedLocal { name } => {
            format!("undefined variable `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::UndefinedModule { name } => {
            format!("undefined module `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::NonGlobalExtern => {
            "non-global functions cannot be extern".to_string()
        }
        LoweringDiagnosticKind::InvalidEscape => "invalid escape".to_string(),
        LoweringDiagnosticKind::ArraySizeMismatch { found, expected } => {
            format!("expected `{}` elements, found `{}`", expected, found)
        }
        LoweringDiagnosticKind::TyParseError(parse_error) => lower_ty_parse_error(parse_error),
    }
}

fn lower_ty_parse_error(d: &TyParseError) -> String {
    match d {
        TyParseError::ArrayMissingSize => "array is missing an explicit size".to_string(),
        TyParseError::ArraySizeNotConst => "array size must be a constant integer".to_string(),
        TyParseError::ArraySizeOutOfBounds => "integer literal out of range".to_string(),
        TyParseError::ArrayHasBody => "array type cannot have a body".to_string(),
        TyParseError::NotATy => "expression cannot be converted into a type".to_string(),
        TyParseError::NonGlobalTy => "tried to use a non-global variable as a type".to_string(),
        TyParseError::NonPrimitive => unreachable!(),
    }
}

fn ty_diagnostic_message(
    d: &TyDiagnostic,
    resolved_arena: &Arena<ResolvedTy>,
    interner: &Interner,
) -> String {
    match &d.kind {
        hir_ty::TyDiagnosticKind::Mismatch { expected, found } => {
            format!(
                "expected `{}` but found `{}`",
                expected.display(resolved_arena, interner),
                found.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::Uncastable { from, to } => {
            format!(
                "cannot cast `{}` to `{}`",
                from.display(resolved_arena, interner),
                to.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::OpMismatch { op, first, second } => {
            format!(
                "`{}` cannot be {} `{}`",
                first.display(resolved_arena, interner),
                match op {
                    hir::BinaryOp::Add => "added to",
                    hir::BinaryOp::Sub => "subtracted by",
                    hir::BinaryOp::Mul => "multiplied by",
                    hir::BinaryOp::Div => "divided by",
                    hir::BinaryOp::Mod => "modulo'ed by",
                    hir::BinaryOp::Lt
                    | hir::BinaryOp::Gt
                    | hir::BinaryOp::Le
                    | hir::BinaryOp::Ge
                    | hir::BinaryOp::Eq
                    | hir::BinaryOp::Ne
                    | hir::BinaryOp::And
                    | hir::BinaryOp::Or => "compared to",
                },
                second.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::IfMismatch { found, expected } => {
            format!(
                "`if` and `else` have different types, expected `{}` but found `{}`",
                found.display(resolved_arena, interner),
                expected.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::IndexMismatch { found } => {
            format!(
                "tried indexing `[]` a non-array, `{}`",
                found.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::IndexOutOfBounds {
            index,
            actual_size,
            array_ty,
        } => {
            format!(
                "index `[{}]` is too big, `{}` has size `{}`",
                index,
                array_ty.display(resolved_arena, interner),
                actual_size,
            )
        }
        hir_ty::TyDiagnosticKind::MismatchedArgCount { found, expected } => {
            format!("expected {} arguments but found {}", expected, found)
        }
        hir_ty::TyDiagnosticKind::CalledNonFunction { found } => {
            format!(
                "expected a function, but found {}",
                found.display(resolved_arena, interner),
            )
        }
        hir_ty::TyDiagnosticKind::DerefMismatch { found } => {
            format!(
                "tried dereferencing `^` a non-pointer, `{}`",
                found.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::MissingElse { expected } => {
            format!(
                "this `if` is missing an `else` with type `{}`",
                expected.display(resolved_arena, interner)
            )
        }
        hir_ty::TyDiagnosticKind::Undefined { name } => {
            format!("undefined type `{}`", interner.lookup(*name))
        }
        hir_ty::TyDiagnosticKind::NotYetResolved { path } => {
            format!(
                "circular definition, `{}` has not yet been resolved",
                path.display(interner),
            )
        }
        hir_ty::TyDiagnosticKind::ParamNotATy => "parameters cannot be used as types".to_string(),
        hir_ty::TyDiagnosticKind::MutableTy => "types cannot be mutable".to_string(),
        hir_ty::TyDiagnosticKind::MutateBinding => "cannot mutate a `::` binding".to_string(),
        hir_ty::TyDiagnosticKind::MutateImmutableRef => {
            "cannot mutate an immutable reference. consider changing it to `^mut`".to_string()
        }
        hir_ty::TyDiagnosticKind::CannotMutate => "cannot mutate immutable data".to_string(),
        hir_ty::TyDiagnosticKind::MutableRefToImmutableData => {
            "cannot get a `^mut` to immutable data".to_string()
        }
    }
}

fn ty_diagnostic_help_message(d: &TyDiagnosticHelp) -> String {
    match &d.kind {
        hir_ty::TyDiagnosticHelpKind::FoundToBeImmutable => {
            "this is found to be immutable".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::ImmutableBinding => {
            "`::` bindings are immutable. consider changing it to `:=`".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::ImmutableRef => {
            "this is an immutable reference. consider changing it to `^mut`".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::ImmutableParam => {
            "parameters are immutable. consider passing a `^mut`".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::ImmutableGlobal => "globals are immutable".to_string(),
    }
}

fn format_kind(kind: TokenKind) -> &'static str {
    match kind {
        TokenKind::Ident => "identifier",
        TokenKind::As => "`as`",
        TokenKind::If => "`if`",
        TokenKind::Else => "`else`",
        TokenKind::While => "`while`",
        TokenKind::Loop => "`loop`",
        TokenKind::Mut => "`mut`",
        TokenKind::Distinct => "`distinct`",
        TokenKind::Extern => "`extern`",
        TokenKind::Bool => "boolean",
        TokenKind::Int => "integer",
        TokenKind::Float => "float",
        TokenKind::Quote => "`\"`",
        TokenKind::Escape => "escape sequence",
        TokenKind::StringContents => "string",
        TokenKind::Plus => "`+`",
        TokenKind::Hyphen => "`-`",
        TokenKind::Asterisk => "`*`",
        TokenKind::Slash => "`/`",
        TokenKind::Percent => "`%`",
        TokenKind::Less => "`<`",
        TokenKind::LessEquals => "`<=`",
        TokenKind::Greater => "`>`",
        TokenKind::GreaterEquals => "`>=`",
        TokenKind::Bang => "`!`",
        TokenKind::BangEquals => "`!=`",
        TokenKind::DoubleAnd => "`&&`",
        TokenKind::DoublePipe => "`||`",
        TokenKind::DoubleEquals => "`==`",
        TokenKind::Equals => "`=`",
        TokenKind::Dot => "`.`",
        TokenKind::Colon => "`:`",
        TokenKind::Comma => "`,`",
        TokenKind::Semicolon => "`;`",
        TokenKind::Arrow => "`->`",
        TokenKind::Caret => "`^`",
        TokenKind::LParen => "`(`",
        TokenKind::RParen => "`)`",
        TokenKind::LBrack => "`[`",
        TokenKind::RBrack => "`]`",
        TokenKind::LBrace => "`{`",
        TokenKind::RBrace => "`}`",
        TokenKind::Whitespace => "whitespace",
        TokenKind::CommentContents | TokenKind::CommentLeader => "comment",
        TokenKind::Error => "an unrecognized token",
    }
}

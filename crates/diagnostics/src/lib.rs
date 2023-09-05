use std::vec;

use ast::validation::{ValidationDiagnostic, ValidationDiagnosticKind};
use hir::{
    IndexingDiagnostic, IndexingDiagnosticKind, LoweringDiagnostic, LoweringDiagnosticKind,
    TyParseError,
};
use hir_ty::{TyDiagnostic, TyDiagnosticHelp};
use interner::Interner;
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
        project_root: &std::path::Path,
        interner: &Interner,
        line_index: &LineIndex,
        with_colors: bool,
    ) -> Vec<String> {
        let range = self.range();

        let (start_line, start_col) = line_index.line_col(range.start());

        // we subtract 1 since end_line_column is inclusive,
        // unlike TextRange which is always exclusive
        let (end_line, end_col) = line_index.line_col(range.end() - TextSize::from(1));

        let (ansi_yellow, ansi_red, ansi_white, ansi_blue) = if with_colors {
            ("\x1B[1;93m", "\x1B[1;91m", "\x1B[1;97m", "\x1B[1;94m")
        } else {
            ("", "", "", "")
        };

        let severity = match self.severity() {
            Severity::Warning => format!("{}warning", ansi_yellow),
            Severity::Error => format!("{}error", ansi_red),
        };

        let mut lines = vec![format!(
            "{}{}: {}",
            severity,
            ansi_white,
            self.message(project_root, interner)
        )];

        input_snippet(
            filename,
            input,
            start_line,
            start_col,
            end_line,
            end_col,
            range,
            &mut lines,
            with_colors,
        );

        if let Some(help) = self.help() {
            lines.push(format!(
                "{}help{}: {}",
                ansi_blue,
                ansi_white,
                help.message(project_root, interner)
            ));

            let range = help.range();

            let (start_line, start_col) = line_index.line_col(range.start());

            // we subtract 1 since end_line_column is inclusive,
            // unlike TextRange which is always exclusive
            let (end_line, end_col) = line_index.line_col(range.end() - TextSize::from(1));

            input_snippet(
                filename,
                input,
                start_line,
                start_col,
                end_line,
                end_col,
                range,
                &mut lines,
                with_colors,
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
            Repr::Ty(d) => {
                if d.is_error() {
                    Severity::Error
                } else {
                    Severity::Warning
                }
            }
        }
    }

    pub fn message(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        match &self.0 {
            Repr::Syntax(e) => syntax_error_message(e),
            Repr::Validation(d) => validation_diagnostic_message(d),
            Repr::Indexing(d) => indexing_diagnostic_message(d, interner),
            Repr::Lowering(d) => lowering_diagnostic_message(d, interner),
            Repr::Ty(d) => ty_diagnostic_message(d, project_root, interner),
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

    pub fn message(&self, project_root: &std::path::Path, interner: &Interner) -> String {
        match &self {
            HelpDiagnostic::Ty(d) => ty_diagnostic_help_message(d, project_root, interner),
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
    with_colors: bool,
) {
    let (ansi_reset, ansi_gray, ansi_yellow) = if with_colors {
        ("\x1B[0m", "\x1B[1;90m", "\x1B[1;93m")
    } else {
        ("", "", "")
    };

    let filename = pathdiff::diff_paths(filename, std::env::current_dir().unwrap())
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|| filename.to_string());

    const PADDING: &str = " | ";
    const POINTER_UP: &str = "^";
    // const POINTER_DOWN: &str = "v";

    let file_lines: Vec<_> = input.lines().collect();

    let is_single_line = start_line == end_line;
    if is_single_line {
        let line_number_padding = " ".repeat(count_digits(start_line.0 + 1, 10));

        lines.push(format!(
            "{}{}--> at {}:{}:{}",
            ansi_gray,
            line_number_padding,
            filename,
            start_line.0 + 1,
            start_col.0 + 1,
        ));

        lines.push(format!("{}{}{}", ansi_gray, line_number_padding, PADDING));

        lines.push(format!(
            "{}{}{}{}{}",
            ansi_gray,
            start_line.0 + 1,
            PADDING,
            ansi_reset,
            file_lines[start_line.0 as usize]
        ));

        lines.push(format!(
            "{}{}{}{}{}{}{}",
            ansi_gray,
            line_number_padding,
            PADDING,
            " ".repeat(start_col.0 as usize),
            ansi_yellow,
            POINTER_UP.repeat(range.len().try_into().unwrap()),
            ansi_reset
        ));

        return;
    }

    // multi-line errors:

    let line_number_padding = " ".repeat(count_digits(end_line.0 + 1, 10));

    lines.push(format!(
        "{}{}--> at {}:{}:{}",
        ansi_gray,
        line_number_padding,
        filename,
        start_line.0 + 1,
        start_col.0 + 1,
    ));

    // blank line
    lines.push(format!("{}{}{}", ansi_gray, line_number_padding, PADDING));

    // now start printing the actual lines of code
    let first_line = file_lines[start_line.0 as usize];
    lines.push(format!(
        "{}{}{}{}{}{}{}{}",
        ansi_gray,
        start_line.0 + 1,
        " ".repeat(count_digits(end_line.0 + 1, 10) - count_digits(start_line.0 + 1, 10)),
        PADDING,
        ansi_yellow,
        "  ",
        ansi_reset,
        first_line
    ));

    // arrow below first line
    lines.push(format!(
        "{}{}{}{}{}{}{}",
        ansi_gray,
        line_number_padding,
        PADDING,
        ansi_yellow,
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
            ansi_gray,
            num + 1,
            " ".repeat(count_digits(end_line.0 + 1, 10) - count_digits(num as u32 + 1, 10)),
            PADDING,
            ansi_yellow,
            "| ",
            ansi_reset,
            file_line
        ));
    }

    let last_line = file_lines[end_line.0 as usize];
    lines.push(format!(
        "{}{}{}{}{}{}{}",
        ansi_gray,
        end_line.0 + 1,
        PADDING,
        ansi_yellow,
        "| ",
        ansi_reset,
        last_line
    ));
    lines.push(format!(
        "{}{}{}{}{}{}{}{}",
        ansi_gray,
        line_number_padding,
        PADDING,
        ansi_yellow,
        "|",
        "_".repeat(end_col.0 as usize + 1),
        POINTER_UP,
        ansi_reset
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
        IndexingDiagnosticKind::AlreadyDefined { name } => {
            format!("name `{}` already defined", interner.lookup(*name))
        }
        IndexingDiagnosticKind::TyParseError(parse_error) => lower_ty_parse_error(parse_error),
    }
}

fn lowering_diagnostic_message(d: &LoweringDiagnostic, interner: &Interner) -> String {
    match &d.kind {
        LoweringDiagnosticKind::OutOfRangeIntLiteral => "integer literal out of range".to_string(),
        LoweringDiagnosticKind::UndefinedRef { name } => {
            format!("undefined reference to `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::NonGlobalExtern => {
            "non-global functions cannot be extern".to_string()
        }
        LoweringDiagnosticKind::InvalidEscape => "invalid escape".to_string(),
        LoweringDiagnosticKind::ArraySizeMismatch { found, expected } => {
            format!("expected `{}` elements, found `{}`", expected, found)
        }
        LoweringDiagnosticKind::ImportMustEndInDotCapy => {
            "capy files must end in `.capy`".to_string()
        }
        LoweringDiagnosticKind::ImportDoesNotExist { file } => {
            format!("`{}` couldn't be found", file)
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
        TyParseError::NonPrimitive => unreachable!(),
    }
}

fn ty_diagnostic_message(
    d: &TyDiagnostic,
    project_root: &std::path::Path,
    interner: &Interner,
) -> String {
    match &d.kind {
        hir_ty::TyDiagnosticKind::Mismatch { expected, found } => {
            format!(
                "expected `{}` but found `{}`",
                expected.display(project_root, interner),
                found.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::Uncastable { from, to } => {
            format!(
                "cannot cast `{}` to `{}`",
                from.display(project_root, interner),
                to.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::BinaryOpMismatch { op, first, second } => {
            format!(
                "`{}` cannot be {} `{}`",
                first.display(project_root, interner),
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
                second.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::UnaryOpMismatch { op, ty } => {
            format!(
                "cannot apply `{}` to `{}`",
                match op {
                    hir::UnaryOp::Neg => '-',
                    hir::UnaryOp::Pos => '+',
                    hir::UnaryOp::Not => '!',
                },
                ty.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::IfMismatch { found, expected } => {
            format!(
                "`if` and `else` have different types, expected `{}` but found `{}`",
                found.display(project_root, interner),
                expected.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::IndexNonArray { found } => {
            format!(
                "tried indexing `[]` a non-array, `{}`",
                found.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::IndexOutOfBounds {
            index,
            actual_size,
            array_ty,
        } => {
            format!(
                "index `[{}]` is too big, `{}` can only be indexed up to `[{}]`",
                index,
                array_ty.display(project_root, interner),
                actual_size - 1,
            )
        }
        hir_ty::TyDiagnosticKind::MismatchedArgCount { found, expected } => {
            format!("expected {} arguments but found {}", expected, found)
        }
        hir_ty::TyDiagnosticKind::CalledNonFunction { found } => {
            format!(
                "expected a function, but found {}",
                found.display(project_root, interner),
            )
        }
        hir_ty::TyDiagnosticKind::DerefNonPointer { found } => {
            format!(
                "tried dereferencing `^` a non-pointer, `{}`",
                found.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::DerefAny => {
            "tried dereferencing `^` a pointer to `any`. try casting it to a different pointer type first".to_string()
        }
        hir_ty::TyDiagnosticKind::MissingElse { expected } => {
            format!(
                "this `if` is missing an `else` with type `{}`",
                expected.display(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::NotYetResolved { path } => {
            format!(
                "circular definition, `{}` has not yet been resolved",
                path.to_string(project_root, interner),
            )
        }
        hir_ty::TyDiagnosticKind::ParamNotATy => "parameters cannot be used as types".to_string(),
        hir_ty::TyDiagnosticKind::LocalTyIsMutable => {
            "local variables cannot be used as types if they are mutable".to_string()
        }
        hir_ty::TyDiagnosticKind::CannotMutate => "cannot mutate immutable data".to_string(),
        hir_ty::TyDiagnosticKind::MutableRefToImmutableData => {
            "cannot get a `^mut` to immutable data".to_string()
        }
        hir_ty::TyDiagnosticKind::IntTooBigForType { found, max, ty } => {
            format!(
                "integer literal `{}` is too big for `{}`, which can only hold up to {}",
                found,
                ty.display(project_root, interner),
                max
            )
        }
        hir_ty::TyDiagnosticKind::UnknownModule { name } => {
            format!(
                "could not find a module named `{}`",
                name.to_string(project_root, interner)
            )
        }
        hir_ty::TyDiagnosticKind::UnknownFqn { fqn } => format!(
            "`{}` does not exist within the module `{}`",
            interner.lookup(fqn.name.0),
            fqn.module.to_string(project_root, interner)
        ),
        hir_ty::TyDiagnosticKind::NonExistentField { field, found_ty } => format!(
            "there is no field `{}` within `{}`",
            interner.lookup(*field),
            found_ty.display(project_root, interner)
        ),
        hir_ty::TyDiagnosticKind::StructLiteralMissingField { field, expected_ty } => format!(
            "`{}` struct literal is missing the field `{}`",
            expected_ty.display(project_root, interner),
            interner.lookup(*field)
        ),
        hir_ty::TyDiagnosticKind::ComptimePointer => {
            "comptime blocks cannot return pointers. the data won't exist at runtime".to_string()
        }
        hir_ty::TyDiagnosticKind::ComptimeType => {
            "comptime blocks cannot return types ... yet ;)".to_string()
        }
        hir_ty::TyDiagnosticKind::GlobalNotConst => {
            "globals must be constant values. try wrapping this in `comptime { ... }`".to_string()
        }
    }
}

fn ty_diagnostic_help_message(
    d: &TyDiagnosticHelp,
    project_root: &std::path::Path,
    interner: &Interner,
) -> String {
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
        hir_ty::TyDiagnosticHelpKind::ImmutableParam { assignment: true } => {
            "parameters are immutable. consider passing a `^mut`".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::ImmutableParam { assignment: false } => {
            "parameters are immutable".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::ImmutableGlobal => "globals are immutable".to_string(),
        hir_ty::TyDiagnosticHelpKind::NotMutatingRefThroughDeref => {
            "this is a reference, to mutate it's inner value add a `^` at the end to dereference it first"
                .to_string()
        }
        hir_ty::TyDiagnosticHelpKind::IfReturnsTypeHere { found } => {
            format!("here, the `if` returns a {}", found.display(project_root, interner))
        }
        hir_ty::TyDiagnosticHelpKind::MutableVariable => {
            "`:=` bindings are immutable. consider changing it to `::`".to_string()
        }
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
        TokenKind::Struct => "`struct`",
        TokenKind::Import => "`import`",
        TokenKind::Comptime => "`comptime`",
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

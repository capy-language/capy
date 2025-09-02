#![allow(clippy::uninlined_format_args)]
#![allow(clippy::too_many_arguments)]

use std::vec;

use ast::validation::{ValidationDiagnostic, ValidationDiagnosticKind};
use hir::{IndexingDiagnostic, IndexingDiagnosticKind, LoweringDiagnostic, LoweringDiagnosticKind};
use hir_ty::{ExpectedTy, InternTyDisplay, TyDiagnostic, TyDiagnosticHelp};
use interner::Interner;
use line_index::{ColNr, LineIndex, LineNr};
use parser::{ExpectedSyntax, SyntaxError, SyntaxErrorKind};
use syntax::NodeKind;
use text_size::{TextRange, TextSize};

#[cfg(feature = "expose_hir_ty")]
pub use hir_ty;

const NOT_STRING_LIT: &str = "this must be a string literal";

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
    Help,
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
        mod_dir: &std::path::Path,
        interner: &Interner,
        line_index: &LineIndex,
        with_colors: bool,
    ) -> Vec<String> {
        let range = self.range();

        let (start_line, start_col) = line_index.line_col(range.start());

        // we subtract 1 since end_line_column is inclusive,
        // unlike TextRange which is always exclusive
        let (end_line, end_col) = line_index.line_col(range.end() - TextSize::from(1));

        let (ansi_reset, ansi_yellow, ansi_red, ansi_white, ansi_blue) = if with_colors {
            (
                "\x1B[0m",
                "\x1B[1;93m",
                "\x1B[1;91m",
                "\x1B[1;97m",
                "\x1B[1;94m",
            )
        } else {
            ("", "", "", "", "")
        };

        let severity = match self.severity() {
            Severity::Help => format!("{}help", ansi_blue),
            Severity::Warning => format!("{}warning", ansi_yellow),
            Severity::Error => format!("{}error", ansi_red),
        };

        let mut lines = vec![format!(
            "{}{}: {}{}",
            severity,
            ansi_white,
            self.message(mod_dir, interner),
            ansi_reset,
        )];

        input_snippet(
            filename,
            input,
            start_line,
            start_col,
            end_line,
            end_col,
            &mut lines,
            self.severity(),
            with_colors,
            self.arrow(),
        );

        if let Some(help) = self.help() {
            lines.push(format!(
                "{}help{}: {}{}",
                ansi_blue,
                ansi_white,
                help.message(mod_dir, interner),
                ansi_reset
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
                &mut lines,
                Severity::Help,
                with_colors,
                false,
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
                kind:
                    SyntaxErrorKind::UnexpectedToken { range, .. }
                    | SyntaxErrorKind::UnexpectedNode { range, .. },
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
            Repr::Lowering(d) => {
                if d.is_error() {
                    Severity::Error
                } else {
                    Severity::Warning
                }
            }
            Repr::Ty(d) => {
                if d.is_error() {
                    Severity::Error
                } else {
                    Severity::Warning
                }
            }
        }
    }

    pub fn arrow(&self) -> bool {
        matches!(
            self.0,
            Repr::Syntax(SyntaxError {
                kind: SyntaxErrorKind::Missing { .. },
                ..
            })
        ) || self.range().len() == TextSize::new(0)
    }

    pub fn message(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match &self.0 {
            Repr::Syntax(e) => syntax_error_message(e),
            Repr::Validation(d) => validation_diagnostic_message(d),
            Repr::Indexing(d) => indexing_diagnostic_message(d, interner),
            Repr::Lowering(d) => lowering_diagnostic_message(d, interner),
            Repr::Ty(d) => ty_diagnostic_message(d, mod_dir, interner),
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

    pub fn message(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match &self {
            HelpDiagnostic::Ty(d) => ty_diagnostic_help_message(d, mod_dir, interner),
        }
    }
}

fn input_snippet(
    filename: &str,
    input: &str,
    start_line: LineNr,
    start_col: ColNr,
    end_line: LineNr,
    end_col: ColNr,
    lines: &mut Vec<String>,
    severity: Severity,
    with_colors: bool,
    missing_arrow: bool,
) {
    let (ansi_reset, ansi_gray, ansi_err) = if with_colors {
        (
            "\x1B[0m",
            "\x1B[90m",
            match severity {
                Severity::Help => "\x1B[94m",
                Severity::Error => "\x1B[91m",
                Severity::Warning => "\x1B[93m",
            },
        )
    } else {
        ("", "", "")
    };

    let filename = pathdiff::diff_paths(filename, std::env::current_dir().unwrap())
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|| filename.to_string());

    const PADDING: &str = " │ ";

    let file_lines: Vec<_> = input.lines().collect();

    let mut max_digits = count_digits(end_line.0 + 3, 10);

    let line_end = end_line.0 as usize + 3;
    let line_start = (start_line.0 as usize).saturating_sub(2);

    // if the selection of text is really really long, omit the middle and put a "..."
    const OMIT_POINT: usize = 5 + 2; // +2 for the extra non-error lines that get shown at the ends

    if line_end - line_start > OMIT_POINT * 2 {
        // make sure max_digits is at least big enough to support the "..."
        max_digits = max_digits.max(3);
    }

    let line_number_padding = " ".repeat(max_digits);

    lines.push(format!(
        "{}{}--> at {}:{}:{}",
        ansi_gray,
        line_number_padding,
        filename,
        start_line.0 + 1,
        start_col.0 + 1,
    ));
    lines.push(String::new());

    for (num, file_line) in file_lines
        .iter()
        .enumerate()
        .take(line_end)
        .skip(line_start)
    {
        if num - line_start >= OMIT_POINT && line_end - num > OMIT_POINT {
            if num - line_start == OMIT_POINT {
                lines.push(format!(
                    "{ansi_err}...{}{}{}",
                    " ".repeat(max_digits - 3),
                    ansi_gray,
                    PADDING,
                ));
            }
            continue;
        }

        let error_line = num >= start_line.0 as usize && num <= end_line.0 as usize;
        let arrow = error_line && missing_arrow;
        let file_line = match (num == start_line.0 as usize, num == end_line.0 as usize) {
            (true, true) => {
                if arrow {
                    format!("{}{}", ansi_reset, file_line)
                } else {
                    format!(
                        "{}{}{}{}{}{}",
                        ansi_reset,
                        &file_line[..start_col.0 as usize],
                        ansi_err,
                        &file_line[start_col.0 as usize..end_col.0 as usize + 1],
                        ansi_reset,
                        &file_line[end_col.0 as usize + 1..],
                    )
                }
            }
            (true, false) => {
                format!(
                    "{}{}{}{}",
                    ansi_reset,
                    &file_line[..start_col.0 as usize],
                    ansi_err,
                    &file_line[start_col.0 as usize..]
                )
            }
            (false, true) => {
                format!(
                    "{}{}{}{}",
                    ansi_err,
                    &file_line[..end_col.0 as usize + 1],
                    ansi_reset,
                    &file_line[end_col.0 as usize + 1..]
                )
            }
            (false, false) if error_line => format!("{}{}", ansi_err, file_line),
            (false, false) => format!("{}{}", ansi_reset, file_line),
        };

        lines.push(format!(
            "{}{:>max_digits$}{}{}{}",
            if error_line { ansi_err } else { ansi_reset },
            num + 1,
            ansi_gray,
            PADDING,
            file_line.replace('\t', "    "),
        ));

        if arrow {
            lines.push(format!(
                "{}{}{}{}{}{}{}",
                ansi_reset,
                " ".repeat(max_digits),
                ansi_gray,
                PADDING,
                " ".repeat(
                    start_col.0 as usize
                        + file_line.chars().filter(|char| *char == '\t').count() * 3
                ),
                ansi_err,
                "^",
            ));
        }
    }

    lines.push(String::new());
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
        ExpectedSyntax::Unnamed(kind) => buf.push_str(kind.to_str()),
    };

    let mut message = String::new();

    match e.kind {
        SyntaxErrorKind::Missing { .. } => {
            message.push_str("missing ");
            write_expected_syntax(&mut message);
        }
        SyntaxErrorKind::UnexpectedToken { found, .. } => {
            message.push_str("expected ");
            write_expected_syntax(&mut message);
            message.push_str(&format!(" but found {}", found.to_str()));
        }
        SyntaxErrorKind::UnexpectedNode { found, .. } => {
            message.push_str("expected ");
            write_expected_syntax(&mut message);
            message.push_str(&format!(" but found {}", format_node(found)));
        }
    }

    message
}

fn validation_diagnostic_message(d: &ValidationDiagnostic) -> String {
    match d.kind {
        ValidationDiagnosticKind::AlwaysTrue => "this is always true".to_string(),
        ValidationDiagnosticKind::AlwaysFalse => "this is always false".to_string(),
        ValidationDiagnosticKind::ParenInCondition => {
            "you can remove the `(` and `)`, conditions don't need parentheses".to_string()
        }
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
        LoweringDiagnosticKind::UndefinedRef { name } => {
            format!("undefined reference to `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::UndefinedLabel { name } => {
            format!("there is no label named `{}`", interner.lookup(*name))
        }
        LoweringDiagnosticKind::NonGlobalExternFunc => {
            "non-global functions cannot be extern".to_string()
        }
        LoweringDiagnosticKind::InvalidEscape => "invalid escape".to_string(),
        LoweringDiagnosticKind::DirectiveMismatchedArgCount { found_count } => {
            if *found_count == 0 {
                "expected an argument of type `str`".to_string()
            } else {
                "expected only 1 argument, but found {found_count}".to_string()
            }
        }
        LoweringDiagnosticKind::DirectiveNonStringArg => NOT_STRING_LIT.to_string(),
        LoweringDiagnosticKind::ModMustBeAlphanumeric => "modules must be alphanumeric".to_string(),
        LoweringDiagnosticKind::ModDoesNotExist { module, mod_dir } => {
            format!("a `{}` module could not be found in `{}`", module, mod_dir)
        }
        LoweringDiagnosticKind::ModDoesNotContainModFile { module, mod_dir } => {
            format!(
                "the `{}` module exists in `{}`, but doesn't contain a `mod.capy` file",
                module, mod_dir
            )
        }
        LoweringDiagnosticKind::ImportMustEndInDotCapy => {
            "capy files must end in `.capy`".to_string()
        }
        LoweringDiagnosticKind::ImportDoesNotExist { file } => {
            format!("`{}` couldn't be found", file)
        }
        LoweringDiagnosticKind::ImportOutsideCWD { file } => {
            format!("`{}` is outside the current working module", file)
        }
        LoweringDiagnosticKind::NonBuiltinLambdaBody => {
            "you can only use `#builtin(...)` for function bodies".to_string()
        }
        LoweringDiagnosticKind::TooManyCharsInCharLiteral => {
            "character literals can only contain one character".to_string()
        }
        LoweringDiagnosticKind::EmptyCharLiteral => {
            "character literals cannot be empty".to_string()
        }
        LoweringDiagnosticKind::NonU8CharLiteral => {
            "character literals cannot contain non-ASCII characters".to_string()
        }
        LoweringDiagnosticKind::ContinueNonLoop { name } => match *name {
            Some(name) => format!(
                "cannot continue from `{}`, a non-loop",
                interner.lookup(name)
            ),
            None => "can only `continue` from loops".to_string(),
        },
        LoweringDiagnosticKind::ReturnFromDefer => {
            "cannot `return` from within a `defer`".to_string()
        }
        LoweringDiagnosticKind::PropagateFromDefer => {
            "cannot use `.try` from within a `defer`".to_string()
        }
        LoweringDiagnosticKind::BreakFromDefer => {
            "cannot `break` to an outer block from within a `defer`".to_string()
        }
        LoweringDiagnosticKind::ContinueFromDefer => {
            "cannot `continue` an outer loop from within a `defer`".to_string()
        }
        LoweringDiagnosticKind::UsingBreakInsteadOfReturn => {
            "this is actually a `break` to the first block, consider using `return` instead"
                .to_string()
        }
        LoweringDiagnosticKind::MultipleDefaultArms => {
            "a switch statement cannot have multiple default arms".to_string()
        }
        LoweringDiagnosticKind::RegularArmAfterDefault => {
            "this arm comes after the default arm `_`, which must be last".to_string()
        }
    }
}

fn ty_diagnostic_message(
    d: &TyDiagnostic,
    mod_dir: &std::path::Path,
    interner: &Interner,
) -> String {
    match &d.kind {
        hir_ty::TyDiagnosticKind::Mismatch { expected, found } => {
            let show_ids = expected
                .get_concrete()
                .is_some_and(|e| e.is_similar_to(found));
            format!(
                "expected {} but found `{}`",
                format_expected_type("a", "value", false, expected, mod_dir, interner, show_ids),
                found.named_display(mod_dir, interner, show_ids)
            )
        }
        hir_ty::TyDiagnosticKind::Uncastable { from, to } => {
            let show_ids = from.is_similar_to(to);
            format!(
                "cannot cast `{}` to `{}`",
                from.named_display(mod_dir, interner, show_ids),
                to.named_display(mod_dir, interner, show_ids)
            )
        }
        hir_ty::TyDiagnosticKind::BinaryOpMismatch { op, first, second } => {
            let show_ids = first.is_similar_to(second);
            format!(
                "`{}` cannot be {} `{}`",
                first.named_display(mod_dir, interner, show_ids),
                match op {
                    hir::BinaryOp::Add => "added to",
                    hir::BinaryOp::Sub => "subtracted by",
                    hir::BinaryOp::Mul => "multiplied by",
                    hir::BinaryOp::Div => "divided by",
                    hir::BinaryOp::Mod => "modulo'd by",
                    hir::BinaryOp::BAnd => "bitwise and'd with",
                    hir::BinaryOp::BOr => "bitwise or'd with",
                    hir::BinaryOp::Xor => "bitwise xor'd with",
                    hir::BinaryOp::LShift => "left shifted with",
                    hir::BinaryOp::RShift => "right shifted with",
                    hir::BinaryOp::Lt
                    | hir::BinaryOp::Gt
                    | hir::BinaryOp::Le
                    | hir::BinaryOp::Ge
                    | hir::BinaryOp::Eq
                    | hir::BinaryOp::Ne => "comapred to",
                    hir::BinaryOp::LAnd => "and'd with",
                    hir::BinaryOp::LOr => "or'd with",
                },
                second.named_display(mod_dir, interner, show_ids)
            )
        }
        hir_ty::TyDiagnosticKind::UnaryOpMismatch { op, ty } => {
            format!(
                "cannot apply `{}` to `{}`",
                match op {
                    hir::UnaryOp::Neg => '-',
                    hir::UnaryOp::Pos => '+',
                    hir::UnaryOp::BNot => '~',
                    hir::UnaryOp::LNot => '!',
                },
                ty.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::IfMismatch { first, second } => {
            let show_ids = first.is_similar_to(second);
            format!(
                "the first branch is `{}` but the second branch is `{}`. they must be the same",
                first.named_display(mod_dir, interner, show_ids),
                second.named_display(mod_dir, interner, show_ids),
            )
        }
        hir_ty::TyDiagnosticKind::SwitchMismatch {
            first,
            other,
        } => {
            let show_ids = first.is_similar_to(other);
            format!(
                "this branch has a type of `{}` but the first branch has a type of `{}`. they must be the same",
                other.named_display(mod_dir, interner, show_ids),
                first.named_display(mod_dir, interner, show_ids),
            )
        }
        hir_ty::TyDiagnosticKind::IndexNonArray { found } => {
            format!(
                "tried indexing a non-array, `{}`",
                found.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::IndexOutOfBounds {
            index,
            actual_size,
            array_ty,
        } => match actual_size.checked_sub(1) {
            Some(up_to) => format!(
                "index `[{}]` is too big, `{}` can only be indexed up to `[{}]`",
                index,
                array_ty.named_display(mod_dir, interner, false),
                up_to,
            ),
            None => format!(
                "index `[{}]` is too big for `{}`",
                index,
                array_ty.named_display(mod_dir, interner, false),
            ),
        },
        hir_ty::TyDiagnosticKind::ExtraArg { found } => {
            format!(
                "found an extra argument of type `{}`",
                found.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::MissingArg { expected } => {
            format!(
                "expected {}",
                format_expected_type("an", "argument", true, expected, mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::CalledNonFunction { found } => {
            format!(
                "expected a function, but found {}",
                found.named_display(mod_dir, interner, false),
            )
        }
        hir_ty::TyDiagnosticKind::DerefNonPointer { found } => {
            format!(
                "tried dereferencing a non-pointer, `{}`",
                found.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::DerefRaw => {
            "tried dereferencing a `rawptr`. try casting it to a different pointer type first"
                .to_string()
        }
        hir_ty::TyDiagnosticKind::IndexRaw => {
            "tried indexing a `rawslice`. try casting it to a different slice type first"
                .to_string()
        }
        hir_ty::TyDiagnosticKind::MissingElse { expected } => {
            format!(
                "this `if` is missing an `else` with type `{}`",
                expected.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::NotYetResolved { fqn } => {
            format!(
                "circular definition, `{}` has not yet been resolved",
                fqn.to_string(mod_dir, interner),
            )
        }
        hir_ty::TyDiagnosticKind::CantUseAsTy => "this cannot be used as a type".to_string(),
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
                ty.named_display(mod_dir, interner, false),
                max
            )
        }
        hir_ty::TyDiagnosticKind::UnknownFile { file } => {
            format!(
                "could not find a file named `{}`",
                file.to_string(mod_dir, interner)
            )
        }
        hir_ty::TyDiagnosticKind::UnknownFqn { fqn } => format!(
            "`{}` does not exist within the file `{}`",
            interner.lookup(fqn.name.0),
            fqn.file.to_string(mod_dir, interner)
        ),
        hir_ty::TyDiagnosticKind::NonExistentMember { member, found_ty } => format!(
            "there is no member named `{}` within `{}`",
            interner.lookup(*member),
            found_ty.named_display(mod_dir, interner, false)
        ),
        hir_ty::TyDiagnosticKind::NotAShorthandVariantOfSumType {
            ty,
            sum_ty: scrutinee_ty,
        } => format!(
            "there is no variant named `{}` within `{}`",
            interner.lookup(*ty),
            scrutinee_ty.named_display(mod_dir, interner, false),
        ),
        hir_ty::TyDiagnosticKind::NotAVariantOfSumType { ty, sum_ty } => format!(
            "the type `{}` is not a variant of `{}`",
            ty.named_display(mod_dir, interner, false),
            sum_ty.named_display(mod_dir, interner, false)
        ),
        hir_ty::TyDiagnosticKind::StructLiteralMissingMember {
            member: field,
            expected_ty,
        } => format!(
            "`{}` struct literal is missing the member `{}`",
            expected_ty.named_display(mod_dir, interner, false),
            interner.lookup(*field)
        ),
        hir_ty::TyDiagnosticKind::ComptimePointer => {
            "comptime blocks cannot return pointers. the data won't exist at runtime".to_string()
        }
        hir_ty::TyDiagnosticKind::GlobalNotConst => {
            "globals must be constant values. try wrapping this in `comptime { ... }`".to_string()
        }
        hir_ty::TyDiagnosticKind::EntryNotFunction => {
            "the entry point must be a function".to_string()
        }
        hir_ty::TyDiagnosticKind::EntryHasParams => {
            "the entry point cannot have any parameters".to_string()
        }
        hir_ty::TyDiagnosticKind::EntryBadReturn => {
            "the entry point must either return `{int}` or `void`".to_string()
        }
        hir_ty::TyDiagnosticKind::ArraySizeNotInt => "array size must be an integer".to_string(),
        hir_ty::TyDiagnosticKind::ArraySizeNotConst => {
            "array size must be known at compile-time".to_string()
        }
        hir_ty::TyDiagnosticKind::DiscriminantNotInt => {
            "discriminants must be an integer".to_string()
        }
        hir_ty::TyDiagnosticKind::DiscriminantNotConst => {
            "discriminants must be known at compile-time".to_string()
        }
        hir_ty::TyDiagnosticKind::DiscriminantUsedAlready { value } => {
            format!("you've already used `{value}` as a discriminant")
        }
        hir_ty::TyDiagnosticKind::ExternGlobalMissingTy => {
            "external globals must have type annotations".to_string()
        }
        hir_ty::TyDiagnosticKind::ExternVarargs => {
            "vararg parameters in Capy are internally represented by slices, and they are not compatable with variadic functions in C"
                .to_string()
        }
        hir_ty::TyDiagnosticKind::DeclTypeHasNoDefault { ty } => {
            format!(
                "`{}` does not have a default value. one must be supplied",
                ty.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::SwitchDoesNotCoverVariant { ty } => {
            format!(
                "this switch statement does not have an arm for `{}`",
                ty.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::SwitchAlreadyCoversVariant { ty } => {
            format!(
                "this switch statement already has an arm for `{}`",
                ty.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
            previous_ty,
            current_ty,
        } => {
            let show_ids = previous_ty.is_similar_to(current_ty);
            format!(
                "the type of this parameter, `{}`, cannot be differentiated from the var arg parameter right behind it, `...{}`",
                current_ty.named_display(mod_dir, interner, show_ids),
                previous_ty.named_display(mod_dir, interner, show_ids)
            )
        }
        hir_ty::TyDiagnosticKind::ImpossibleToDifferentiateErrorUnion {
            error_ty,
            payload_ty,
        } => {
            let show_ids = error_ty.is_similar_to(payload_ty);
            format!(
                "the error type, `{}`, is too similar to the payload type, `{}`",
                error_ty.named_display(mod_dir, interner, show_ids),
                payload_ty.named_display(mod_dir, interner, show_ids)
            )
        }
        hir_ty::TyDiagnosticKind::UnknownDirective { name } => format!(
            "there is no compiler directive named `#{}`",
            interner.lookup(*name)
        ),
        hir_ty::TyDiagnosticKind::PropagateNonPropagatable { found } => {
            format!(
                "can only use `.try` on optionals or error unions. this is `{}`",
                found.named_display(mod_dir, interner, false)
            )
        }
        hir_ty::TyDiagnosticKind::NotABuiltin { name } => {
            format!(
                "`{}` is not a compiler built-in value or function",
                interner.lookup(*name)
            )
        }
        hir_ty::TyDiagnosticKind::NotStringLit => NOT_STRING_LIT.to_string(),
        hir_ty::TyDiagnosticKind::BuiltinFunctionMismatch {
            builtin_name,
            expected,
            found,
        } => {
            let show_ids = expected.is_similar_to(found);
            format!(
                "`#builtin(\"{}\")` has a type of `{}` but this function is `{}`",
                interner.lookup(*builtin_name),
                expected.named_display(mod_dir, interner, show_ids),
                found.named_display(mod_dir, interner, show_ids)
            )
        }
    }
}

fn ty_diagnostic_help_message(
    d: &TyDiagnosticHelp,
    mod_dir: &std::path::Path,
    interner: &Interner,
) -> String {
    // todo: if the regular message showed ids, the help message should as well
    match &d.kind {
        hir_ty::TyDiagnosticHelpKind::CannotMutateExpr => {
            "this expression cannot be mutated".to_string()
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
            format!("here, the `if` returns a `{}`", found.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::MutableVariable => {
            "`:=` bindings are mutable. consider changing it to `::`".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::TailExprReturnsHere => {
            "this is the actual value that is being returned".to_string()
        }
        hir_ty::TyDiagnosticHelpKind::BreakHere { ty, is_default: false } => {
            format!("a value of `{}` was expected because of this earlier break", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::ReturnHere { ty, is_default: false } => {
            format!("a value of `{}` was expected because of this earlier return", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::BreakHere { ty, is_default: true } => {
            format!("`{}` was expected because this earlier break didn't have a value", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::ReturnHere { ty, is_default: true } => {
            format!("`{}` was expected because this earlier return didn't have a value", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::PropagateHere { ty } => {
            format!("a value of `{}` was expected because it might be returned by this earlier `.try`", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::AnnotationHere { ty } => {
            format!("a value of `{}` was expected because of this annotation", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::ReturnTyHere { ty, is_default: false } => {
            format!("a value of `{}` was expected because of this return type", ty.named_display(mod_dir, interner, false))
        }
        hir_ty::TyDiagnosticHelpKind::ReturnTyHere { ty, is_default: true } => {
            format!("`{}` was expected expected because there is no return type", ty.named_display(mod_dir, interner, false))
        }
    }
}

// fn format_kind(kind: TokenKind) -> &'static str {
//     match kind {
//         TokenKind::Ident => "identifier",
//         TokenKind::As => "`as`",
//         TokenKind::If => "`if`",
//         TokenKind::Else => "`else`",
//         TokenKind::While => "`while`",
//         TokenKind::Loop => "`loop`",
//         TokenKind::Switch => "`switch`",
//         TokenKind::In => "`in`",
//         TokenKind::Mut => "`mut`",
//         TokenKind::Distinct => "`distinct`",
//         TokenKind::Extern => "`extern`",
//         TokenKind::Struct => "`struct`",
//         TokenKind::Enum => "`enum`",
//         TokenKind::Import => "`import`",
//         TokenKind::Mod => "`mod`",
//         TokenKind::Comptime => "`comptime`",
//         TokenKind::Return => "`return`",
//         TokenKind::Break => "`break`",
//         TokenKind::Continue => "`continue`",
//         TokenKind::Defer => "`defer`",
//         TokenKind::Bool => "boolean",
//         TokenKind::Int => "integer",
//         TokenKind::Hex => "hex literal",
//         TokenKind::Bin => "binary literal",
//         TokenKind::Float => "float",
//         TokenKind::SingleQuote => "`'`",
//         TokenKind::DoubleQuote => "`\"`",
//         TokenKind::Escape => "escape sequence",
//         TokenKind::StringContents => "string",
//         TokenKind::Plus => "`+`",
//         TokenKind::Hyphen => "`-`",
//         TokenKind::Asterisk => "`*`",
//         TokenKind::Slash => "`/`",
//         TokenKind::Percent => "`%`",
//         TokenKind::Left => "`<`",
//         TokenKind::DoubleLeft => "`<<`",
//         TokenKind::LeftEquals => "`<=`",
//         TokenKind::Right => "`>`",
//         TokenKind::DoubleRight => "`>>`",
//         TokenKind::RightEquals => "`>=`",
//         TokenKind::Bang => "`!`",
//         TokenKind::BangEquals => "`!=`",
//         TokenKind::And => "`&`",
//         TokenKind::DoubleAnd => "`&&`",
//         TokenKind::Pipe => "`|`",
//         TokenKind::DoublePipe => "`||`",
//         TokenKind::DoubleEquals => "`==`",
//         TokenKind::Tilde => "`~`",
//         TokenKind::Equals => "`=`",
//         TokenKind::Dot => "`.`",
//         TokenKind::Ellipsis => "`...`",
//         TokenKind::Colon => "`:`",
//         TokenKind::Comma => "`,`",
//         TokenKind::Semicolon => "`;`",
//         TokenKind::Arrow => "`->`",
//         TokenKind::FatArrow => "`=>`",
//         TokenKind::Caret => "`^`",
//         TokenKind::Backtick => "'`'", // this one is a little weird lol
//         TokenKind::LParen => "`(`",
//         TokenKind::RParen => "`)`",
//         TokenKind::LBrack => "`[`",
//         TokenKind::RBrack => "`]`",
//         TokenKind::LBrace => "`{`",
//         TokenKind::RBrace => "`}`",
//         TokenKind::Whitespace => "whitespace",
//         TokenKind::NonBreakingSpace => "non-breaking space character",
//         TokenKind::CommentContents | TokenKind::CommentLeader => "comment",
//         TokenKind::Error => "an unrecognized token",
//     }
// }

fn format_node(kind: NodeKind) -> &'static str {
    // since this is only currently used for `array_size`, it's fine to just leave everything else
    // as unimplemented!()
    match kind {
        NodeKind::ArraySize => "array size",
        NodeKind::CastExpr => "`as`",
        _ => unimplemented!(),
    }
}

fn format_expected_type(
    article: &str,
    name: &str,
    add_type: bool,
    expected: &ExpectedTy,
    mod_dir: &std::path::Path,
    interner: &Interner,
    show_ids: bool,
) -> String {
    match expected {
        hir_ty::ExpectedTy::Concrete(expected) => {
            format!(
                "{article} {name} of {}`{}`",
                if add_type || **expected == hir_ty::Ty::Type {
                    "type "
                } else {
                    ""
                },
                expected.named_display(mod_dir, interner, show_ids),
            )
        }
        hir_ty::ExpectedTy::Enum => "an enum".to_string(),
        hir_ty::ExpectedTy::SumType => "an enum, optional, or error union".to_string(),
    }
}

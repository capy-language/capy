#![allow(clippy::uninlined_format_args)]
#![allow(clippy::too_many_arguments)]

mod globals;
mod ty;

#[cfg(test)]
mod tests;

use std::str::FromStr;

use globals::{ExprExpected, GlobalInferenceCtx};
use hir::{FQComptime, FQLambda, FileName};
use interner::{Interner, Key};
use internment::Intern;
use itertools::Itertools;
use la_arena::{ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use text_size::TextRange;

use topo::TopoSort;
pub use ty::*;

macro_rules! trait_alias {
    ($vis:vis $name:ident : $trait:path) => {
        $vis trait $name: $trait {}

        impl<T: $trait> $name for T {}
    };
}

pub(crate) use trait_alias;

pub(crate) type InferResult<T> = Result<T, Vec<Inferrable>>;

#[derive(Debug, Clone, Default)]
pub struct ProjectInference {
    signatures: FxHashMap<hir::Fqn, Signature>,
    files: FxHashMap<hir::FileName, FileInference>,
}

impl std::ops::Index<hir::Fqn> for ProjectInference {
    type Output = Signature;

    fn index(&self, fqn: hir::Fqn) -> &Self::Output {
        &self.signatures[&fqn]
    }
}

impl std::ops::Index<hir::FileName> for ProjectInference {
    type Output = FileInference;

    fn index(&self, module: hir::FileName) -> &Self::Output {
        &self.files[&module]
    }
}

impl std::ops::IndexMut<hir::FileName> for ProjectInference {
    fn index_mut(&mut self, module: hir::FileName) -> &mut Self::Output {
        self.files.get_mut(&module).unwrap()
    }
}

#[derive(Debug, Clone, Default)]
pub struct FileInference {
    expr_tys: ArenaMap<Idx<hir::Expr>, Intern<Ty>>,
    /// the actual types of type expressions
    meta_tys: ArenaMap<Idx<hir::Expr>, Intern<Ty>>,
    local_tys: ArenaMap<Idx<hir::LocalDef>, Intern<Ty>>,
    switch_local_tys: ArenaMap<Idx<hir::SwitchArg>, Intern<Ty>>,
}

impl FileInference {
    pub fn get_meta_ty(&self, expr: Idx<hir::Expr>) -> Option<Intern<Ty>> {
        self.meta_tys.get(expr).copied()
    }

    pub fn try_get_expr(&self, expr: Idx<hir::Expr>) -> Option<Intern<Ty>> {
        self.expr_tys.get(expr).copied()
    }
}

impl std::ops::Index<Idx<hir::Expr>> for FileInference {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        &self.expr_tys[expr]
    }
}

impl std::ops::IndexMut<Idx<hir::Expr>> for FileInference {
    #[track_caller]
    fn index_mut(&mut self, expr: Idx<hir::Expr>) -> &mut Self::Output {
        self.expr_tys.get_mut(expr).unwrap()
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for FileInference {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, local_def: Idx<hir::LocalDef>) -> &Self::Output {
        &self.local_tys[local_def]
    }
}

impl std::ops::Index<Idx<hir::SwitchArg>> for FileInference {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, switch_local: Idx<hir::SwitchArg>) -> &Self::Output {
        &self.switch_local_tys[switch_local]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Signature(pub Intern<Ty>);

#[cfg(test)]
use derivative::Derivative;

#[derive(Clone)]
#[cfg_attr(not(test), derive(Debug, PartialEq))]
#[cfg_attr(test, derive(Derivative))]
#[cfg_attr(test, derivative(Debug, PartialEq))]
pub struct TyDiagnostic {
    pub kind: TyDiagnosticKind,
    pub file: hir::FileName,
    // it's important to set this as `Some(_)` as much as possible,
    // even if the given expression isn't technically the source of the error.
    // this field is used for scanning through a group of expressions to see if they have any
    // related errors (so it can be decided whether or not to attempt to compile them).
    // only set this to None if there truly isn't a related expression.
    #[cfg_attr(test, derivative(Debug = "ignore", PartialEq = "ignore"))]
    pub expr: Option<Idx<hir::Expr>>,
    pub range: TextRange,
    pub help: Option<TyDiagnosticHelp>,
}

impl TyDiagnostic {
    pub fn eq_ignore_expr(&self, other: &TyDiagnostic) -> bool {
        self.kind == other.kind
            && self.file == other.file
            && self.range == other.range
            && self.help == other.help
    }

    pub fn is_error(&self) -> bool {
        // !matches!(self.kind, TyDiagnosticKind::IntTooBigForType { .. })
        true
    }
}

/// Sometimes a specific type is expected, and sometimes it's something vague like "an enum"
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedTy {
    Concrete(Intern<Ty>),
    Enum,
    /// This matches any value whose type might vary, not including `any`
    /// e.g. an enum, an optional, an error union.
    ///
    /// Anything that could internally get compiled to a tagged union
    SumType,
}

impl ExpectedTy {
    pub fn get_concrete(self) -> Option<Intern<Ty>> {
        match self {
            Self::Concrete(ty) => Some(ty),
            _ => None,
        }
    }

    pub fn can_take(self, found: &Ty) -> bool {
        match self {
            Self::Concrete(expected) => found.can_fit_into(&expected),
            Self::Enum => found.is_enum(),
            Self::SumType => found.is_sum_ty(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyDiagnosticKind {
    Mismatch {
        expected: ExpectedTy,
        found: Intern<Ty>,
    },
    Uncastable {
        from: Intern<Ty>,
        to: Intern<Ty>,
    },
    BinaryOpMismatch {
        op: hir::BinaryOp,
        first: Intern<Ty>,
        second: Intern<Ty>,
    },
    UnaryOpMismatch {
        op: hir::UnaryOp,
        ty: Intern<Ty>,
    },
    // todo: IfMismatch and SwitchMismatch should be help diags
    IfMismatch {
        first: Intern<Ty>,
        second: Intern<Ty>,
    },
    SwitchMismatch {
        first: Intern<Ty>,
        other: Intern<Ty>,
    },
    NotAShorthandVariantOfSumType {
        ty: Key,
        sum_ty: Intern<Ty>,
    },
    NotAVariantOfSumType {
        ty: Intern<Ty>,
        sum_ty: Intern<Ty>,
    },
    IndexNonArray {
        found: Intern<Ty>,
    },
    IndexOutOfBounds {
        index: u64,
        actual_size: u64,
        array_ty: Intern<Ty>,
    },
    PropagateNonPropagatable {
        found: Intern<Ty>,
    },
    ExtraArg {
        found: Intern<Ty>,
    },
    MissingArg {
        expected: ExpectedTy,
    },
    CalledNonFunction {
        found: Intern<Ty>,
    },
    DerefNonPointer {
        found: Intern<Ty>,
    },
    DerefRaw,
    IndexRaw,
    MissingElse {
        expected: Intern<Ty>,
    },
    CannotMutate,
    MutableRefToImmutableData,
    NotYetResolved {
        fqn: hir::Fqn,
    },
    CantUseAsTy,
    /// this is a more specific case of `CantUseAsTy` that shows more information
    ParamNotATy,
    LocalTyIsMutable,
    IntTooBigForType {
        found: u64,
        max: u64,
        ty: Intern<Ty>,
    },
    UnknownFile {
        file: FileName,
    },
    UnknownFqn {
        fqn: hir::Fqn,
    },
    NonExistentMember {
        member: Key,
        found_ty: Intern<Ty>,
    },
    StructLiteralMissingMember {
        member: Key,
        expected_ty: Intern<Ty>,
    },
    ComptimePointer,
    GlobalNotConst,
    EntryNotFunction,
    EntryHasParams,
    EntryBadReturn,
    ArraySizeNotInt,
    ArraySizeNotConst,
    DiscriminantNotInt,
    DiscriminantNotConst,
    DiscriminantUsedAlready {
        value: u64,
    },
    ExternGlobalMissingTy,
    ExternVarargs,
    DeclTypeHasNoDefault {
        ty: Intern<Ty>,
    },
    SwitchDoesNotCoverVariant {
        ty: Intern<Ty>,
    },
    SwitchAlreadyCoversVariant {
        ty: Intern<Ty>,
    },
    ImpossibleToDifferentiateVarArgs {
        previous_ty: Intern<Ty>,
        current_ty: Intern<Ty>,
    },
    ImpossibleToDifferentiateErrorUnion {
        error_ty: Intern<Ty>,
        payload_ty: Intern<Ty>,
    },
    UnknownDirective {
        name: Key,
    },
    NotABuiltin {
        name: Key,
    },
    NotStringLit,
    BuiltinFunctionMismatch {
        builtin_name: Key,
        expected: Intern<Ty>,
        found: Intern<Ty>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TyDiagnosticHelp {
    pub kind: TyDiagnosticHelpKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyDiagnosticHelpKind {
    CannotMutateExpr,
    ImmutableBinding,
    ImmutableRef,
    ImmutableParam {
        assignment: bool,
    },
    ImmutableGlobal,
    NotMutatingRefThroughDeref,
    IfReturnsTypeHere {
        found: Intern<Ty>,
    },
    MutableVariable,
    TailExprReturnsHere,
    BreakHere {
        ty: Intern<Ty>,
        is_default: bool,
    },
    /// this refers to `return` statements
    ReturnHere {
        ty: Intern<Ty>,
        is_default: bool,
    },
    PropagateHere {
        ty: Intern<Ty>,
    },
    AnnotationHere {
        ty: Intern<Ty>,
    },
    /// this refers to declared return types like `-> i32`
    ReturnTyHere {
        ty: Intern<Ty>,
        is_default: bool,
    },
}

// todo: I want to make this more expansive. `Data` should be removed and
// there should be variants for structs, arrays, etc. This will allow indexing
// and member access at compile-time.
#[derive(Debug, Clone)]
pub enum ComptimeResult {
    Type(Intern<Ty>),
    Integer { num: u64, bit_width: u8 },
    Float { num: f64, bit_width: u8 },
    Data(Box<[u8]>),
    Void,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Inferrable {
    Global(hir::Fqn),
    Lambda(FQLambda),
}

impl Inferrable {
    fn to_string(self, interner: &Interner) -> String {
        match self {
            Inferrable::Global(fqn) => fqn.to_string(std::path::Path::new(""), interner),
            Inferrable::Lambda(lambda) => format!(
                "lambda {} #{}",
                lambda.file.debug(interner),
                lambda.expr.into_raw()
            ),
        }
    }

    fn file(&self) -> FileName {
        match self {
            Inferrable::Global(fqn) => fqn.file,
            Inferrable::Lambda(fql) => fql.file,
        }
    }
}

trait_alias! {
    pub EvalComptimeFn:
    FnMut(FQComptime, &ProjectInference) -> ComptimeResult
}

pub struct InferenceResult {
    pub tys: ProjectInference,
    pub diagnostics: Vec<TyDiagnostic>,
    pub any_were_unsafe_to_compile: bool,
}

pub struct InferenceCtx<'a, F: EvalComptimeFn> {
    world_index: &'a hir::WorldIndex,
    world_bodies: &'a hir::WorldBodies,
    interner: &'a Interner,
    tys: ProjectInference,
    all_inferred: FxHashSet<Inferrable>,
    to_infer: TopoSort<Inferrable>,
    inferred_stmts: FxHashSet<(hir::FileName, Idx<hir::Stmt>)>,
    diagnostics: Vec<TyDiagnostic>,
    eval_comptime: F,
}

impl<'a, F: EvalComptimeFn> InferenceCtx<'a, F> {
    pub fn new(
        world_index: &'a hir::WorldIndex,
        world_bodies: &'a hir::WorldBodies,
        interner: &'a Interner,
        eval_comptime: F,
    ) -> Self {
        Self {
            world_index,
            world_bodies,
            interner,
            diagnostics: Vec::new(),
            tys: Default::default(),
            all_inferred: Default::default(),
            to_infer: Default::default(),
            inferred_stmts: Default::default(),
            eval_comptime,
        }
    }

    /// only pass `None` to `entry_point` if your testing type checking and you don't want to worry
    /// about the entry point
    pub fn finish(
        mut self,
        entry_point: Option<hir::Fqn>,
        track_unsafe_to_compile: bool,
    ) -> InferenceResult {
        for (module, _) in self.world_index.get_all_files() {
            self.tys.files.insert(module, FileInference::default());
        }

        self.to_infer.extend(
            self.world_index
                .get_all_files()
                .into_iter()
                .flat_map(|(file, index)| {
                    index
                        .definitions()
                        .map(move |name| Inferrable::Global(hir::Fqn { file, name }))
                        .sorted()
                }), // .inspect(|to_infer| {
                    //     print!("{to_infer:?}");
                    //     match to_infer {
                    //         Inferrable::Global(fqn) => {
                    //             println!(" {}", fqn.debug(self.interner))
                    //         }
                    //         Inferrable::Lambda(_) => {}
                    //     }
                    // }),
        );

        if self.to_infer.is_empty() {
            return InferenceResult {
                tys: self.tys,
                diagnostics: self.diagnostics,
                any_were_unsafe_to_compile: false,
            };
        }

        const DEBUG: bool = false;

        loop {
            if DEBUG {
                println!("another loop");
            }

            let leaves = match self.to_infer.peek_all() {
                Ok(leaves) => leaves.into_iter().cloned().collect_vec(),
                Err(_) => {
                    let mut cyclic = self
                        .to_infer
                        .peek_all_cyclic()
                        .unwrap()
                        .into_iter()
                        .cloned()
                        .collect_vec();

                    // todo: sometimes the order of what is evaluated can change the errors a lot
                    // (see tests::get_const_on_cyclic_globals)
                    // for now i'm gonna sort this list, but maybe a different solution would be
                    // better

                    cyclic.sort();

                    let nyr = Signature(Ty::NotYetResolved.into());

                    for inferrable in &cyclic {
                        println!("cyclic: {:?}", inferrable);
                        if let Inferrable::Global(fqn) = inferrable {
                            self.tys.signatures.insert(*fqn, nyr);
                        }
                    }

                    cyclic
                }
            };

            assert!(!leaves.is_empty());

            for inferrable in leaves {
                if DEBUG {
                    println!("- {}", inferrable.to_string(self.interner));
                }

                match self.infer(inferrable) {
                    Ok(_) => {
                        self.to_infer.remove(&inferrable);
                    }
                    Err(deps) => {
                        self.to_infer.insert_deps(inferrable, deps);
                    }
                }
            }

            if self.to_infer.is_empty() {
                break;
            }
        }

        let mut any_were_unsafe_to_compile = false;

        if track_unsafe_to_compile {
            for fqn in self
                .all_inferred
                .clone()
                .into_iter()
                .filter_map(|i| match i {
                    Inferrable::Global(fqn) => Some(fqn),
                    _ => None,
                })
            {
                if self.world_bodies.is_extern(fqn) {
                    continue;
                }

                let mut global_ctx = GlobalInferenceCtx {
                    file: fqn.file,
                    currently_inferring: Inferrable::Global(fqn),
                    world_index: self.world_index,
                    world_bodies: self.world_bodies,
                    bodies: &self.world_bodies[fqn.file],
                    interner: self.interner,
                    expected_tys: Default::default(),
                    local_usages: Default::default(),
                    tys: &mut self.tys,
                    param_tys: Vec::new(),
                    all_inferred: &self.all_inferred,
                    inferred_stmts: &mut self.inferred_stmts,
                    to_infer: &mut self.to_infer,
                    diagnostics: &mut self.diagnostics,
                    eval_comptime: &mut self.eval_comptime,
                };

                let body = self.world_bodies.body(fqn);
                let ty = self.world_bodies.ty(fqn);

                if !global_ctx.is_safe_to_compile(body).unwrap()
                    || ty.is_some_and(|ty| !global_ctx.is_safe_to_compile(ty).unwrap())
                {
                    println!(
                        "{} is unsafe to compile",
                        fqn.to_string(std::path::Path::new(""), self.interner)
                    );
                    any_were_unsafe_to_compile = true;
                }
            }
        }

        'entry: {
            if let Some(entry_point) = entry_point {
                let range = match self
                    .world_index
                    .ranges()
                    .find(|(fqn, _)| *fqn == entry_point)
                {
                    Some((_, range)) => range,
                    None => break 'entry,
                };

                let ty = self.tys.signatures[&entry_point].0;

                if let Some((param_tys, return_ty)) = ty.as_function() {
                    let lambda = match self.world_bodies[entry_point.file]
                        [self.world_bodies.body(entry_point)]
                    {
                        hir::Expr::Lambda(lambda) => &self.world_bodies[entry_point.file][lambda],
                        _ => todo!("entry point doesn't have lambda body"),
                    };

                    if !param_tys.is_empty() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::EntryHasParams,
                            file: entry_point.file,
                            // `None` because the correctness of the entry point
                            // will not affect the compilability of this global.
                            // `is_safe_to_compile` should return true for this global.
                            expr: None,
                            range: lambda.params_range,
                            help: None,
                        });
                    }

                    if !return_ty.is_void() && !return_ty.is_int() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::EntryBadReturn,
                            file: entry_point.file,
                            expr: None,
                            // unwrap is safe because if the return type didn't exist, it'd be void
                            range: self.world_bodies[entry_point.file]
                                .range_for_expr(lambda.return_ty.unwrap()),
                            help: None,
                        });
                    }
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::EntryNotFunction,
                        file: entry_point.file,
                        expr: None,
                        range: range.whole,
                        help: None,
                    });
                }
            }
        }

        self.tys.shrink_to_fit();

        InferenceResult {
            tys: self.tys,
            diagnostics: self.diagnostics,
            any_were_unsafe_to_compile,
        }
    }

    fn infer(&mut self, inferrable: Inferrable) -> InferResult<()> {
        if self.all_inferred.contains(&inferrable) {
            return Ok(());
        }

        match inferrable {
            Inferrable::Global(fqn) => self.infer_fqn(fqn)?,
            Inferrable::Lambda(lambda) => self.infer_lambda(lambda)?,
        }

        self.all_inferred.insert(inferrable);

        Ok(())
    }

    fn infer_fqn(&mut self, fqn: hir::Fqn) -> InferResult<()> {
        let mut global_ctx = GlobalInferenceCtx {
            file: fqn.file,
            currently_inferring: Inferrable::Global(fqn),
            world_index: self.world_index,
            world_bodies: self.world_bodies,
            bodies: &self.world_bodies[fqn.file],
            interner: self.interner,
            expected_tys: Default::default(),
            local_usages: Default::default(),
            inferred_stmts: &mut self.inferred_stmts,
            tys: &mut self.tys,
            param_tys: Default::default(),
            all_inferred: &self.all_inferred,
            to_infer: &mut self.to_infer,
            diagnostics: &mut self.diagnostics,
            eval_comptime: &mut self.eval_comptime,
        };

        let had_previous = global_ctx.tys.signatures.contains_key(&fqn);

        if !had_previous {
            // we do this before parsing the possible type annotation to avoid a recursion like this:
            // a : a : 5;
            global_ctx
                .tys
                .signatures
                .insert(fqn, Signature(Intern::new(Ty::NotYetResolved)));
        }

        let ty_annotation = match self.world_bodies.ty(fqn) {
            Some(ty_expr) => match global_ctx.const_ty(ty_expr) {
                Ok(ty) => Some(ExprExpected {
                    expected_ty: ty,
                    annotation_range: global_ctx.bodies.range_for_expr(ty_expr),
                    is_return_ty: false,
                    is_default: false,
                }),
                Err(why) => {
                    global_ctx.tys.signatures.remove(&fqn);
                    return Err(why);
                }
            },
            None => None,
        };

        if self.world_bodies.is_extern(fqn) {
            let ty_annotation = match ty_annotation {
                Some(expected) => expected.expected_ty,
                None => {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ExternGlobalMissingTy,
                        file: fqn.file,
                        expr: None,
                        range: self.world_index.range_info(fqn).whole,
                        help: None,
                    });

                    Ty::Unknown.into()
                }
            };

            self.tys.signatures.insert(fqn, Signature(ty_annotation));

            return Ok(());
        }

        let body = self.world_bodies.body(fqn);

        // we don't need to do anything fancy to allow recursion.
        // the `infer_surface` stage should have already figured out the
        // signature of every function, including this one.

        let ty = match global_ctx.finish_body(body, ty_annotation, true) {
            Ok(ty) => ty,
            Err(why) => {
                global_ctx.tys.signatures.remove(&fqn);
                return Err(why);
            }
        };

        self.tys.signatures.insert(fqn, Signature(ty));

        Ok(())
    }

    fn infer_lambda(&mut self, fql: FQLambda) -> InferResult<()> {
        let hir::Lambda {
            body,
            return_ty: return_ty_expr,
            params_range,
            ..
        } = self.world_bodies[fql.file][fql.lambda];

        let fn_type = self.tys[fql.file][fql.expr];

        match body {
            hir::LambdaBody::Extern => {}
            hir::LambdaBody::Empty => {
                assert_eq!(return_ty_expr, None);
                // an error will have been reported
            }
            hir::LambdaBody::Builtin {
                name,
                literal_range,
            } => {
                let Ok(kind) = BuiltinKind::from_str(self.interner.lookup(name)) else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::NotABuiltin { name },
                        file: fql.file,
                        expr: Some(fql.expr),
                        range: literal_range,
                        help: None,
                    });

                    return Ok(());
                };

                let expected = kind.to_expected();

                if !fn_type.can_fit_into(&expected) {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::BuiltinFunctionMismatch {
                            builtin_name: name,
                            expected,
                            found: fn_type,
                        },
                        file: fql.file,
                        expr: Some(fql.expr),
                        range: self.world_bodies[fql.file].range_for_expr(fql.expr),
                        help: None,
                    });
                }
            }
            hir::LambdaBody::Block(block) => {
                // todo: does this range look good?
                let return_ty_range = return_ty_expr
                    .map(|return_ty_expr| {
                        self.world_bodies[fql.file].range_for_expr(return_ty_expr)
                    })
                    .unwrap_or_else(|| TextRange::new(params_range.end(), params_range.end()));

                let (param_tys, return_ty) = self.tys[fql.file][fql.expr].as_function().unwrap();

                let mut global_ctx = GlobalInferenceCtx {
                    file: fql.file,
                    currently_inferring: Inferrable::Lambda(fql),
                    world_index: self.world_index,
                    world_bodies: self.world_bodies,
                    bodies: &self.world_bodies[fql.file],
                    interner: self.interner,
                    expected_tys: Default::default(),
                    local_usages: Default::default(),
                    inferred_stmts: &mut self.inferred_stmts,
                    tys: &mut self.tys,
                    param_tys,
                    all_inferred: &self.all_inferred,
                    to_infer: &mut self.to_infer,
                    diagnostics: &mut self.diagnostics,
                    eval_comptime: &mut self.eval_comptime,
                };

                global_ctx.finish_body(
                    block,
                    Some(ExprExpected {
                        expected_ty: return_ty,
                        annotation_range: return_ty_range,
                        is_return_ty: true,
                        is_default: return_ty_expr.is_none(),
                    }),
                    false,
                )?;
            }
        }

        Ok(())
    }
}

impl ProjectInference {
    /// This might be slightly superficial in some scenarios, I'm not sure
    pub fn all_tys(&self) -> impl Iterator<Item = Intern<Ty>> + '_ {
        self.signatures
            .values()
            .map(|Signature(ty)| *ty)
            .chain(self.files.values().flat_map(|tys| {
                tys.meta_tys
                    .values()
                    .copied()
                    .chain(tys.expr_tys.values().copied())
                    .chain(tys.local_tys.values().copied())
            }))
            .unique()
    }

    fn shrink_to_fit(&mut self) {
        let Self {
            signatures,
            files: modules,
        } = self;
        signatures.shrink_to_fit();
        modules.shrink_to_fit();
    }

    pub fn debug(
        &self,
        mod_dir: &std::path::Path,
        interner: &Interner,
        include_mods: bool,
        fancy: bool,
    ) -> String {
        let mut s = String::new();

        let mut signatures = self
            .signatures
            .iter()
            .filter(|(fqn, _)| include_mods || !fqn.file.is_mod(mod_dir, interner))
            .map(|(fqn, sig)| (fqn.to_string(mod_dir, interner), sig))
            .collect::<Vec<_>>();

        signatures.sort_by(|(fqn1, _), (fqn2, _)| fqn1.cmp(fqn2));

        for (fqn, sig) in signatures {
            s.push_str(&fqn);
            s.push_str(" : ");
            s.push_str(&format!(
                "{}\n",
                sig.0.named_display(mod_dir, interner, true)
            ));
        }

        let mut files = self
            .files
            .iter()
            .filter(|(fqn, _)| include_mods || !fqn.is_mod(mod_dir, interner))
            .collect::<Vec<_>>();
        files.sort_by_key(|(name, _)| **name);

        for (name, tys) in files {
            if fancy || self.files.len() > 1 {
                s.push_str(&format!("{}:\n", name.to_string(mod_dir, interner)));
            }
            for (expr_idx, ty) in tys.expr_tys.iter() {
                if fancy {
                    s.push_str(&format!("  \x1B[90m#{}\x1B[0m", expr_idx.into_raw(),));
                } else {
                    if self.files.len() > 1 {
                        s.push_str("  ");
                    }
                    s.push_str(&format!("{}", expr_idx.into_raw(),));
                }
                s.push_str(&format!(
                    " : {}\n",
                    ty.named_display(mod_dir, interner, true)
                ));
            }

            for (local_def_idx, ty) in tys.local_tys.iter() {
                if fancy || self.files.len() > 1 {
                    s.push_str("  ");
                }
                s.push_str(&format!(
                    "l{} : {}\n",
                    local_def_idx.into_raw(),
                    ty.named_display(mod_dir, interner, true)
                ));
            }
        }

        s
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinSubKind {
    Array,
    Slice,
    Pointer,
    Distinct,
    Struct,
    Enum,
    Variant,
    Optional,
    ErrorUnion,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinKind {
    PtrToRaw { opt: bool },
    PtrFromRaw { mutable: bool, opt: bool },
    MetaToRaw,
    LayoutSlice { sub_kind: BuiltinSubKind },
    SingleLayout { sub_kind: BuiltinSubKind },
    InfoSlice { sub_kind: BuiltinSubKind },
    CommandlineArgs,
}

impl BuiltinKind {
    fn to_expected(self) -> Intern<Ty> {
        match self {
            BuiltinKind::PtrToRaw { opt } => Ty::Function {
                param_tys: if opt {
                    vec![ParamTy {
                        ty: Ty::Optional {
                            sub_ty: Ty::RawPtr { mutable: false }.into(),
                        }
                        .into(),
                        varargs: false,
                        impossible_to_differentiate: false,
                    }]
                } else {
                    vec![ParamTy {
                        ty: Ty::RawPtr { mutable: false }.into(),
                        varargs: false,
                        impossible_to_differentiate: false,
                    }]
                },
                return_ty: Ty::UInt(u8::MAX).into(),
            }
            .into(),
            BuiltinKind::PtrFromRaw { mutable, opt } => Ty::Function {
                param_tys: vec![ParamTy {
                    ty: Ty::UInt(u8::MAX).into(),
                    varargs: false,
                    impossible_to_differentiate: false,
                }],
                return_ty: if opt {
                    Ty::Optional {
                        sub_ty: Ty::RawPtr { mutable }.into(),
                    }
                    .into()
                } else {
                    Ty::RawPtr { mutable }.into()
                },
            }
            .into(),
            BuiltinKind::MetaToRaw => Ty::Function {
                param_tys: vec![ParamTy {
                    ty: Ty::Type.into(),
                    varargs: false,
                    impossible_to_differentiate: false,
                }],
                return_ty: Ty::UInt(32).into(),
            }
            .into(),
            BuiltinKind::LayoutSlice { .. } => Ty::Slice {
                sub_ty: Ty::AnonStruct {
                    members: vec![
                        MemberTy {
                            name: hir::Name(Key::size()),
                            ty: Ty::UInt(u8::MAX).into(),
                        },
                        MemberTy {
                            name: hir::Name(Key::align()),
                            ty: Ty::UInt(u8::MAX).into(),
                        },
                    ],
                }
                .into(),
            }
            .into(),

            BuiltinKind::SingleLayout { .. } => Ty::AnonStruct {
                members: vec![
                    MemberTy {
                        name: hir::Name(Key::size()),
                        ty: Ty::UInt(u8::MAX).into(),
                    },
                    MemberTy {
                        name: hir::Name(Key::align()),
                        ty: Ty::UInt(u8::MAX).into(),
                    },
                ],
            }
            .into(),
            BuiltinKind::InfoSlice { sub_kind } => Ty::Slice {
                sub_ty: Ty::AnonStruct {
                    members: match sub_kind {
                        BuiltinSubKind::Array => vec![
                            MemberTy {
                                name: hir::Name(Key::len()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                        ],
                        BuiltinSubKind::Slice => vec![MemberTy {
                            name: hir::Name(Key::sub_ty()),
                            ty: Ty::Type.into(),
                        }],
                        BuiltinSubKind::Pointer => vec![
                            MemberTy {
                                name: hir::Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::mutable()),
                                ty: Ty::Bool.into(),
                            },
                        ],
                        BuiltinSubKind::Distinct => vec![MemberTy {
                            name: hir::Name(Key::sub_ty()),
                            ty: Ty::Type.into(),
                        }],
                        BuiltinSubKind::Struct => vec![MemberTy {
                            name: hir::Name(Key::members()),
                            ty: Ty::Slice {
                                sub_ty: Ty::AnonStruct {
                                    members: vec![
                                        MemberTy {
                                            name: hir::Name(Key::name()),
                                            ty: Ty::String.into(),
                                        },
                                        MemberTy {
                                            name: hir::Name(Key::ty()),
                                            ty: Ty::Type.into(),
                                        },
                                        MemberTy {
                                            name: hir::Name(Key::offset()),
                                            ty: Ty::UInt(u8::MAX).into(),
                                        },
                                    ],
                                }
                                .into(),
                            }
                            .into(),
                        }],
                        BuiltinSubKind::Enum => vec![
                            MemberTy {
                                name: hir::Name(Key::variants()),
                                ty: Ty::Slice {
                                    sub_ty: Ty::Type.into(),
                                }
                                .into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::discriminant_offset()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                        ],
                        BuiltinSubKind::Variant => vec![
                            MemberTy {
                                name: hir::Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::discriminant()),
                                ty: Ty::UInt(32).into(),
                            },
                        ],
                        BuiltinSubKind::Optional => vec![
                            MemberTy {
                                name: hir::Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::is_non_zero()),
                                ty: Ty::Bool.into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::discriminant_offset()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                        ],
                        BuiltinSubKind::ErrorUnion => vec![
                            MemberTy {
                                name: hir::Name(Key::error_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::payload_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: hir::Name(Key::discriminant_offset()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                        ],
                    },
                }
                .into(),
            }
            .into(),
            BuiltinKind::CommandlineArgs => Ty::Slice {
                sub_ty: Ty::String.into(),
            }
            .into(),
        }
    }
}

impl FromStr for BuiltinKind {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "const_rawptr_to_usize" => Ok(BuiltinKind::PtrToRaw { opt: false }),
            "usize_to_const_rawptr" => Ok(BuiltinKind::PtrFromRaw {
                mutable: false,
                opt: false,
            }),
            "usize_to_mut_rawptr" => Ok(BuiltinKind::PtrFromRaw {
                mutable: true,
                opt: false,
            }),

            "opt_const_rawptr_to_usize" => Ok(BuiltinKind::PtrToRaw { opt: true }),
            "usize_to_opt_const_rawptr" => Ok(BuiltinKind::PtrFromRaw {
                mutable: false,
                opt: true,
            }),
            "usize_to_opt_mut_rawptr" => Ok(BuiltinKind::PtrFromRaw {
                mutable: true,
                opt: true,
            }),

            "meta_type_to_u32" => Ok(BuiltinKind::MetaToRaw),

            "array_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::Array,
            }),
            "distinct_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::Distinct,
            }),
            "struct_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::Struct,
            }),
            "enum_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::Enum,
            }),
            "variant_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::Variant,
            }),
            "optional_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::Optional,
            }),
            "error_union_layouts" => Ok(BuiltinKind::LayoutSlice {
                sub_kind: BuiltinSubKind::ErrorUnion,
            }),

            "pointer_layout" => Ok(BuiltinKind::SingleLayout {
                sub_kind: BuiltinSubKind::Pointer,
            }),

            "array_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Array,
            }),
            "slice_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Slice,
            }),
            "pointer_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Pointer,
            }),
            "distinct_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Distinct,
            }),
            "struct_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Struct,
            }),
            "enum_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Enum,
            }),
            "variant_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Variant,
            }),
            "optional_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::Optional,
            }),
            "error_union_infos" => Ok(BuiltinKind::InfoSlice {
                sub_kind: BuiltinSubKind::ErrorUnion,
            }),

            "commandline_args" => Ok(BuiltinKind::CommandlineArgs),

            _ => Err(()),
        }
    }
}

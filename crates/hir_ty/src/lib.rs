mod globals;
mod ty;

use globals::GlobalInferenceCtx;
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
    switch_local_tys: ArenaMap<Idx<hir::SwitchLocal>, Intern<Ty>>,
}

impl FileInference {
    pub fn get_meta_ty(&self, expr: Idx<hir::Expr>) -> Option<Intern<Ty>> {
        self.meta_tys.get(expr).copied()
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

impl std::ops::Index<Idx<hir::SwitchLocal>> for FileInference {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, switch_local: Idx<hir::SwitchLocal>) -> &Self::Output {
        &self.switch_local_tys[switch_local]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Signature(pub Intern<Ty>);

#[derive(Clone, PartialEq)]
#[cfg_attr(not(test), derive(Debug))]
#[cfg_attr(test, derive(derivative::Derivative), derivative(Debug))]
pub struct TyDiagnostic {
    pub kind: TyDiagnosticKind,
    pub file: hir::FileName,
    // it's important to set this as `Some(_)` as much as possible,
    // even if the given expression isn't technically the source of the error.
    // this field is used for scanning through a group of expressions to see if they have any
    // related errors (so it can be decided whether or not to attempt to compile them).
    // only set this to None if there truly isn't a related expression.
    #[cfg_attr(test, derivative(Debug = "ignore"))]
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
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExpectedTy {
    Concrete(Intern<Ty>),
    Enum,
    Variant,
}

#[derive(Debug, Clone, PartialEq)]
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
    IfMismatch {
        first: Intern<Ty>,
        second: Intern<Ty>,
    },
    SwitchMismatch {
        first: Intern<Ty>,
        second: Intern<Ty>,
    },
    NonExistentVariant {
        variant_name: Key,
        enum_ty: Intern<Ty>,
    },
    IndexNonArray {
        found: Intern<Ty>,
    },
    IndexOutOfBounds {
        index: u64,
        actual_size: u64,
        array_ty: Intern<Ty>,
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
    IndexRaw {
        // set this if it is an array, leave `None` if slice
        size: Option<u64>,
    },
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
    DeclTypeHasNoDefault {
        ty: Intern<Ty>,
    },
    SwitchDoesNotCoverVariant {
        ty: Intern<Ty>,
    },
    ImpossibleToDifferentiateVarArgs {
        previous_ty: Intern<Ty>,
        current_ty: Intern<Ty>,
    },
    UnknownDirective {
        name: Key,
    },
    UnwrapVariantMismatchEnum {
        variant_ty: Intern<Ty>,
        enum_ty: Intern<Ty>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct TyDiagnosticHelp {
    pub kind: TyDiagnosticHelpKind,
    pub range: TextRange,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyDiagnosticHelpKind {
    FoundToBeImmutable,
    ImmutableBinding,
    ImmutableRef,
    ImmutableParam { assignment: bool },
    ImmutableGlobal,
    NotMutatingRefThroughDeref,
    IfReturnsTypeHere { found: Intern<Ty> },
    MutableVariable,
    TailExprReturnsHere,
    BreakHere { break_ty: Intern<Ty> },
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
            Some(ty) => match global_ctx.const_ty(ty) {
                Ok(ty) => Some(ty),
                Err(why) => {
                    global_ctx.tys.signatures.remove(&fqn);
                    return Err(why);
                }
            },
            None => None,
        };

        if self.world_bodies.is_extern(fqn) {
            let ty_annotation = match ty_annotation {
                Some(ty) => ty,
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
            body, is_extern, ..
        } = self.world_bodies[fql.file][fql.lambda];

        if is_extern {
            return Ok(());
        }

        let (param_tys, return_ty) = self.tys[fql.file][fql.expr].as_function().unwrap();

        let mut global_ctx = GlobalInferenceCtx {
            file: fql.file,
            currently_inferring: Inferrable::Lambda(fql),
            world_index: self.world_index,
            world_bodies: self.world_bodies,
            bodies: &self.world_bodies[fql.file],
            interner: self.interner,
            local_usages: Default::default(),
            inferred_stmts: &mut self.inferred_stmts,
            tys: &mut self.tys,
            param_tys,
            all_inferred: &self.all_inferred,
            to_infer: &mut self.to_infer,
            diagnostics: &mut self.diagnostics,
            eval_comptime: &mut self.eval_comptime,
        };

        global_ctx.finish_body(body, Some(return_ty), false)?;

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
            s.push_str(&format!("{}\n", sig.0.display(mod_dir, interner)));
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
                s.push_str(&format!(" : {}\n", ty.display(mod_dir, interner)));
            }

            for (local_def_idx, ty) in tys.local_tys.iter() {
                if fancy || self.files.len() > 1 {
                    s.push_str("  ");
                }
                s.push_str(&format!(
                    "l{} : {}\n",
                    local_def_idx.into_raw(),
                    ty.display(mod_dir, interner)
                ));
            }
        }

        s
    }
}

impl Ty {
    pub fn display(&self, mod_dir: &std::path::Path, interner: &Interner) -> String {
        match self {
            Self::NotYetResolved => "!".to_string(),
            Self::Unknown => "<unknown>".to_string(),
            Self::IInt(bit_width) => match *bit_width {
                u8::MAX => "isize".to_string(),
                0 => "{int}".to_string(),
                _ => format!("i{}", bit_width),
            },
            Self::UInt(bit_width) => match *bit_width {
                u8::MAX => "usize".to_string(),
                0 => "{uint}".to_string(),
                _ => format!("u{}", bit_width),
            },
            Self::Float(bit_width) => match *bit_width {
                0 => "{float}".to_string(),
                _ => format!("f{}", bit_width),
            },
            Self::Bool => "bool".to_string(),
            Self::String => "str".to_string(),
            Self::Char => "char".to_string(),
            Self::Array {
                anonymous,
                size,
                sub_ty,
            } => {
                format!(
                    "[{size}]{}{}",
                    if *anonymous { "~" } else { "" },
                    sub_ty.display(mod_dir, interner)
                )
            }
            Self::Slice { sub_ty } => format!("[]{}", sub_ty.display(mod_dir, interner)),
            Self::Pointer { mutable, sub_ty } => {
                format!(
                    "^{}{}",
                    if *mutable { "mut " } else { "" },
                    sub_ty.display(mod_dir, interner)
                )
            }
            Self::Distinct { fqn: Some(fqn), .. } => fqn.to_string(mod_dir, interner),
            Self::Distinct {
                fqn: None,
                uid,
                sub_ty: ty,
            } => {
                format!("distinct'{} {}", uid, ty.display(mod_dir, interner))
            }
            Self::Function {
                param_tys: params,
                return_ty,
            } => {
                let mut res = "(".to_string();

                for (idx, param) in params.iter().enumerate() {
                    if param.varargs {
                        res.push_str("...");
                    }

                    res.push_str(&param.ty.display(mod_dir, interner));

                    if idx != params.len() - 1 {
                        res.push_str(", ");
                    }
                }
                res.push_str(") -> ");
                res.push_str(&return_ty.display(mod_dir, interner));

                res
            }
            Self::Struct { fqn: Some(fqn), .. } => fqn.to_string(mod_dir, interner),
            Self::Struct {
                anonymous,
                fqn: None,
                uid,
                members,
            } => {
                let mut res = if *anonymous {
                    "struct ~{".to_string()
                } else {
                    format!("struct'{} {{", uid)
                };

                for (idx, MemberTy { name, ty }) in members.iter().enumerate() {
                    res.push_str(interner.lookup(name.0));
                    res.push_str(": ");

                    res.push_str(&ty.display(mod_dir, interner));

                    if idx != members.len() - 1 {
                        res.push_str(", ");
                    }
                }

                res.push('}');

                res
            }
            Self::Enum { fqn: Some(fqn), .. } => fqn.to_string(mod_dir, interner),
            Self::Enum {
                fqn: None,
                uid,
                variants,
            } => {
                let mut res = format!("enum '{uid} {{");

                for (idx, variant_ty) in variants.iter().enumerate() {
                    let Ty::Variant {
                        variant_name,
                        sub_ty,
                        discriminant,
                        ..
                    } = variant_ty.as_ref()
                    else {
                        unreachable!("the variants of an enum should be `Ty::Variant`")
                    };

                    res.push_str(interner.lookup(variant_name.0));

                    if !sub_ty.is_void() {
                        res.push_str(": ");
                        res.push_str(&sub_ty.display(mod_dir, interner));
                    }

                    res.push_str(&format!(" | {discriminant}"));

                    if idx != variants.len() - 1 {
                        res.push_str(", ");
                    }
                }

                res.push('}');

                res
            }
            Self::Variant {
                enum_fqn,
                variant_name,
                uid,
                ..
            } => {
                let mut res = String::new();

                if let Some(enum_fqn) = enum_fqn {
                    res.push_str(&enum_fqn.to_string(mod_dir, interner));
                }

                res.push('.');
                res.push_str(interner.lookup(variant_name.0));

                if enum_fqn.is_none() {
                    res.push_str(&format!("'{uid}"));
                }

                res
            }
            Self::Type => "type".to_string(),
            Self::Any => "any".to_string(),
            Self::RawPtr { mutable: false } => "rawptr".to_string(),
            Self::RawPtr { mutable: true } => "mut rawptr".to_string(),
            Self::RawSlice => "rawslice".to_string(),
            Self::Void => "void".to_string(),
            Self::File(file_name) => {
                format!("file {}", file_name.to_string(mod_dir, interner))
            }
            Self::NoEval => "noeval".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{path::Path, vec};

    use super::*;
    use ast::AstNode;
    use codegen::Verbosity;
    use expect_test::{expect, Expect};
    use interner::Interner;
    use target_lexicon::Triple;
    use uid_gen::UIDGenerator;

    #[track_caller]
    fn check<const N: usize>(
        input: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(
            &mut Interner,
        ) -> [(
            TyDiagnosticKind,
            std::ops::Range<u32>,
            Option<(TyDiagnosticHelpKind, std::ops::Range<u32>)>,
        ); N],
    ) {
        check_impl(input, expect, expected_diagnostics, None)
    }

    fn check_impl<const N: usize>(
        input: &str,
        expect: Expect,
        expected_diagnostics: impl Fn(
            &mut Interner,
        ) -> [(
            TyDiagnosticKind,
            std::ops::Range<u32>,
            Option<(TyDiagnosticHelpKind, std::ops::Range<u32>)>,
        ); N],
        entry_point: Option<&str>,
    ) {
        let modules = test_utils::split_multi_module_test_data(input);
        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        let mut uid_gen = UIDGenerator::default();
        let mut world_bodies = hir::WorldBodies::default();

        let mut parse_diags = Vec::<parser::SyntaxError>::new();
        let mut index_diags = Vec::new();
        let mut lowering_diags = Vec::new();

        for (name, text) in &modules {
            if *name == "main.capy" {
                continue;
            }

            let tokens = lexer::lex(text);
            let parse = parser::parse_source_file(&tokens, text);
            parse_diags.extend(parse.errors());
            let tree = parse.into_syntax_tree();

            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, _) = hir::index(root, &tree, &mut interner);

            let module = hir::FileName(interner.intern(name));

            let (bodies, _) = hir::lower(
                root,
                &tree,
                Path::new(name),
                &index,
                &mut uid_gen,
                &mut interner,
                Path::new(""),
                true,
            );
            let debug = bodies.debug(module, std::path::Path::new(""), &interner, true, true);
            if !debug.is_empty() {
                println!("{}", debug);
            }
            world_index.add_file(module, index);
            world_bodies.add_file(module, bodies);
        }

        let text = &modules["main.capy"];
        let module = hir::FileName(interner.intern("main.capy"));
        let tokens = lexer::lex(text);
        let parse = parser::parse_source_file(&tokens, text);
        parse_diags.extend(parse.errors());

        let tree = parse.into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();

        let (index, d) = hir::index(root, &tree, &mut interner);
        index_diags.extend(d);

        let (bodies, d) = hir::lower(
            root,
            &tree,
            Path::new("main"),
            &index,
            &mut uid_gen,
            &mut interner,
            Path::new(""),
            true,
        );
        let debug = bodies.debug(module, std::path::Path::new(""), &interner, true, true);
        if !debug.is_empty() {
            println!("{}", debug);
        }
        lowering_diags.extend(d);
        world_index.add_file(module, index);
        world_bodies.add_file(module, bodies);

        let entry_point = entry_point.map(|entry_point| hir::Fqn {
            file: module,
            name: hir::Name(interner.intern(entry_point)),
        });

        let mut comptime_results = FxHashMap::default();

        let InferenceResult {
            tys,
            diagnostics: actual_diagnostics,
            any_were_unsafe_to_compile,
        } = InferenceCtx::new(&world_index, &world_bodies, &interner, |comptime, tys| {
            codegen::eval_comptime_blocks(
                Verbosity::AllFunctions {
                    include_disasm: true,
                },
                vec![comptime],
                &mut comptime_results,
                Path::new(""),
                &interner,
                &world_bodies,
                // transmute to get past cyclic dependencies
                #[allow(clippy::missing_transmute_annotations)]
                unsafe {
                    std::mem::transmute(tys)
                },
                Triple::host().pointer_width().unwrap().bits(),
            );

            unsafe { std::mem::transmute(comptime_results[&comptime].clone()) }
        })
        .finish(entry_point, true);

        expect.assert_eq(&tys.debug(Path::new(""), &interner, true, false));

        let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
            .into_iter()
            .map(|(kind, range, help)| TyDiagnostic {
                kind,
                file: module,
                expr: None,
                range: TextRange::new(range.start.into(), range.end.into()),
                help: help.map(|(kind, range)| TyDiagnosticHelp {
                    kind,
                    range: TextRange::new(range.start.into(), range.end.into()),
                }),
            })
            .collect();

        let expected_diagnostics_text = format!("{:#?}", expected_diagnostics);
        let actual_diagnostics_text = format!("{:#?}", actual_diagnostics);

        let (dist, changeset) =
            text_diff::diff(&expected_diagnostics_text, &actual_diagnostics_text, "");

        if dist != 0 {
            let mut diff = String::new();
            for seq in changeset {
                match &seq {
                    text_diff::Difference::Same(x) => {
                        diff.push_str(x);
                    }
                    text_diff::Difference::Add(x) => {
                        diff.push_str("\x1B[32;4m");
                        diff.push_str(x);
                        diff.push_str("\x1b[0m");
                    }
                    text_diff::Difference::Rem(x) => {
                        diff.push_str("\x1b[31;4m");
                        diff.push_str(x);
                        diff.push_str("\x1b[0m");
                    }
                }
            }

            println!(
                "expected:\n{}\n\nactual:\n{}\n\ndiff:\n{}\n",
                expected_diagnostics_text, actual_diagnostics_text, diff
            );

            panic!("expected diagnostics are not equal to actual diagnostics");
        }

        let actual_diagnostics = actual_diagnostics
            .into_iter()
            .filter(|d| d.expr.is_some() && d.is_error())
            .collect_vec();

        let any_errs = !parse_diags.is_empty()
            || !index_diags.is_empty()
            || !lowering_diags.is_empty()
            || !actual_diagnostics.is_empty();

        if any_errs != any_were_unsafe_to_compile {
            if !any_errs {
                println!("no errors");
            }
            if !parse_diags.is_empty() {
                println!("parse errors: {:#?}", parse_diags);
            }
            if !index_diags.is_empty() {
                println!("index errors: {:#?}", index_diags);
            }
            if !lowering_diags.is_empty() {
                println!("lowering errors: {:#?}", lowering_diags);
            }
            if !actual_diagnostics.is_empty() {
                println!("type errors: {:#?}", actual_diagnostics);
            }
            println!("anything was unsafe: {}", any_were_unsafe_to_compile);

            if !any_errs {
                panic!("no errors but unsafe to compile");
            } else {
                panic!("errors but safe to compile");
            }
        }
    }

    #[test]
    fn empty_file() {
        check(
            "",
            expect![[r#"
"#]],
            |_| [],
        )
    }

    #[test]
    fn unit_function() {
        check(
            r#"
                foo :: () {};
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn function_with_return_ty() {
        check(
            r#"
                one :: () -> i32 { 1 };
            "#,
            expect![[r#"
                main::one : () -> i32
                1 : i32
                2 : i32
                3 : () -> i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn function_with_float_return_ty() {
        check(
            r#"
                one :: () -> f32 { 1.0 };
            "#,
            expect![[r#"
                main::one : () -> f32
                1 : f32
                2 : f32
                3 : () -> f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn function_with_float_return_ty_int_body() {
        check(
            r#"
                one :: () -> f32 { 1 };
            "#,
            expect![[r#"
                main::one : () -> f32
                1 : f32
                2 : f32
                3 : () -> f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn ty_in_other_file() {
        check(
            r#"
                #- main.capy
                numbers :: #import("numbers.capy");

                fun :: () -> numbers.imaginary {
                    foo : numbers.imaginary = 0;

                    my_magic := numbers.Magic_Struct.{
                        mystical_field = numbers.imaginary.(123),
                    };

                    my_magic.mystical_field
                }
                #- numbers.capy
                imaginary :: distinct i32;

                Magic_Struct :: struct {
                    mystical_field: imaginary,
                };
            "#,
            expect![[r#"
                main::fun : () -> numbers::imaginary
                main::numbers : file numbers
                numbers::Magic_Struct : type
                numbers::imaginary : type
                numbers:
                  1 : type
                  3 : type
                main:
                  0 : file numbers
                  1 : file numbers
                  3 : file numbers
                  5 : numbers::imaginary
                  6 : file numbers
                  8 : numbers::imaginary
                  9 : file numbers
                  11 : numbers::imaginary
                  12 : numbers::Magic_Struct
                  13 : numbers::Magic_Struct
                  14 : numbers::imaginary
                  15 : numbers::imaginary
                  16 : () -> numbers::imaginary
                  l0 : numbers::imaginary
                  l1 : numbers::Magic_Struct
            "#]],
            |_| [],
        );
    }

    #[test]
    fn alias_ty() {
        check(
            r#"
                Foo :: distinct i32;
                Bar :: Foo;

                fun :: () -> Foo {
                    x : Bar = 42;

                    x
                }
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::fun : () -> main::Foo
                1 : type
                2 : type
                5 : main::Foo
                6 : main::Foo
                7 : main::Foo
                8 : () -> main::Foo
                l0 : main::Foo
            "#]],
            |_| [],
        );
    }

    #[test]
    fn alias_ty_in_other_file() {
        check(
            r#"
                #- main.capy
                foo :: #import("foo.capy");

                Foo :: foo.Foo;

                fun :: () -> Foo {
                    foo : Foo = 0;

                    foo
                }
                #- foo.capy
                Foo :: distinct i32;
            "#,
            expect![[r#"
                foo::Foo : type
                main::Foo : type
                main::foo : file foo
                main::fun : () -> foo::Foo
                foo:
                  1 : type
                main:
                  0 : file foo
                  1 : file foo
                  2 : type
                  5 : foo::Foo
                  6 : foo::Foo
                  7 : foo::Foo
                  8 : () -> foo::Foo
                  l0 : foo::Foo
            "#]],
            |_| [],
        );
    }

    #[test]
    fn non_existent_global_in_other_file() {
        check(
            r#"
                #- main.capy
                foo :: #import("foo.capy");
                bar :: foo.bar;

                fun :: () {
                    x : bar = 0;
                }
                #- foo.capy
                // nothing here
            "#,
            expect![[r#"
                main::bar : <unknown>
                main::foo : file foo
                main::fun : () -> void
                foo:
                main:
                  0 : file foo
                  1 : file foo
                  2 : <unknown>
                  4 : {uint}
                  5 : void
                  6 : () -> void
                  l0 : <unknown>
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::UnknownFqn {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("foo.capy")),
                            name: hir::Name(i.intern("bar")),
                        },
                    },
                    67..74,
                    None,
                )]
            },
        );
    }

    #[test]
    fn binary_expr() {
        check(
            r#"
                twenty :: () -> u8 { 10 + 10 };
            "#,
            expect![[r#"
                main::twenty : () -> u8
                1 : u8
                2 : u8
                3 : u8
                4 : u8
                5 : () -> u8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_diff_types() {
        check(
            r#"
                calc :: () -> isize {
                    num1 := i128.(4);
                    num2 := u16.(8);
                    num1 + num2
                };
            "#,
            expect![[r#"
                main::calc : () -> isize
                1 : i128
                3 : i128
                4 : u16
                6 : u16
                7 : i128
                8 : u16
                9 : i128
                10 : i128
                11 : () -> isize
                l0 : i128
                l1 : u16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_uint_type() {
        check(
            r#"
                calc :: () -> u128 {
                    num1 := u16.(4);
                    num1 + 8
                };
            "#,
            expect![[r#"
                main::calc : () -> u128
                1 : u16
                3 : u16
                4 : u16
                5 : u16
                6 : u16
                7 : u16
                8 : () -> u128
                l0 : u16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_int_type() {
        check(
            r#"
                calc :: () -> i128 {
                    num1: u16 = 4;
                    num1 + -8
                };
            "#,
            expect![[r#"
                main::calc : () -> i128
                2 : u16
                3 : u16
                4 : i128
                5 : i128
                6 : i128
                7 : i128
                8 : () -> i128
                l0 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: Ty::UInt(16).into(),
                        second: Ty::IInt(0).into(),
                    },
                    93..102,
                    None,
                )]
            },
        );
    }

    #[test]
    fn cast() {
        check(
            r#"
                check :: () -> bool {
                    num := 5;
                    is_true := bool.(num);
                    is_true
                };
            "#,
            expect![[r#"
                main::check : () -> bool
                1 : {uint}
                2 : {uint}
                4 : bool
                5 : bool
                6 : bool
                7 : () -> bool
                l0 : {uint}
                l1 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cast_unrelated() {
        check(
            r#"
                how_old :: () -> usize {
                    name := "Gandalf";
                    age := usize.(name);
                    age
                };
            "#,
            expect![[r#"
                main::how_old : () -> usize
                1 : str
                2 : str
                4 : usize
                5 : usize
                6 : usize
                7 : () -> usize
                l0 : str
                l1 : usize
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::String.into(),
                        to: Ty::UInt(u8::MAX).into(),
                    },
                    108..120,
                    None,
                )]
            },
        );
    }

    #[test]
    fn strong_int_to_float() {
        check(
            r#"
                main :: () {
                    foo : u16 = 5;

                    bar : f32 = foo;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : u16
                3 : u16
                4 : void
                5 : () -> void
                l0 : u16
                l1 : f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn weak_int_to_float() {
        check(
            r#"
                main :: () {
                    foo : f32 = 5;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : f32
                2 : void
                3 : () -> void
                l0 : f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_float_and_float() {
        check(
            r#"
                main :: () {
                    foo : f32 = 5;
                    bar : f64 = 10;

                    foo + bar;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : f32
                3 : f64
                4 : f32
                5 : f64
                6 : f64
                7 : void
                8 : () -> void
                l0 : f32
                l1 : f64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_strong_int_and_strong_float() {
        check(
            r#"
                main :: () {
                    foo : i32 = 5;
                    bar : f64 = 10;

                    foo + bar;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                3 : f64
                4 : i32
                5 : f64
                6 : f64
                7 : void
                8 : () -> void
                l0 : i32
                l1 : f64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_int_and_strong_float() {
        check(
            r#"
                main :: () {
                    foo : f64 = 10;

                    5 + foo;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : f64
                2 : f64
                3 : f64
                4 : f64
                5 : void
                6 : () -> void
                l0 : f64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_int_and_weak_float() {
        check(
            r#"
                main :: () {
                    5 + 10.0;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {float}
                1 : {float}
                2 : {float}
                3 : void
                4 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_simple_by_annotation() {
        check(
            r#"
                main :: () {
                    num1 := 5;
                    num2 := num1;
                    num3 : usize = num2;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : usize
                1 : usize
                3 : usize
                4 : void
                5 : () -> void
                l0 : usize
                l1 : usize
                l2 : usize
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array() {
        check(
            r#"
                main :: () {
                    my_array := i32.[4, 8, 15, 16, 23, 42];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : [6]i32
                8 : void
                9 : () -> void
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_ty_with_size() {
        check(
            r#"
                main :: () {
                    my_array : [6] i32 = i32.[1, 2, 3, 4, 5, 6];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : usize
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : i32
                9 : i32
                10 : [6]i32
                11 : void
                12 : () -> void
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_ty_with_global_size() {
        check(
            r#"
                size : usize : 3;

                main :: () {
                    my_array : [size] i32 = i32.[1, 2, 3];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                main::size : usize
                1 : usize
                2 : usize
                6 : i32
                7 : i32
                8 : i32
                9 : [3]i32
                10 : void
                11 : () -> void
                l0 : [3]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_ty_with_imported_global_size() {
        check(
            r#"
                #- main.capy

                other :: #import("other.capy");

                main :: () {
                    my_array : [other.size] bool = bool.[true, false];
                };

                #- other.capy

                size : usize : 2;
            "#,
            expect![[r#"
                main::main : () -> void
                main::other : file other
                other::size : usize
                other:
                  1 : usize
                main:
                  0 : file other
                  1 : file other
                  2 : usize
                  6 : bool
                  7 : bool
                  8 : [2]bool
                  9 : void
                  10 : () -> void
                  l0 : [2]bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_ty_with_extern_global_size() {
        check(
            r#"
                size : usize : extern;

                main :: () {
                    my_array : [size] i32 = i32.[];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                main::size : usize
                1 : usize
                5 : [0]i32
                6 : void
                7 : () -> void
                l0 : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::ArraySizeNotConst, 102..106, None)],
        );
    }

    #[test]
    fn array_ty_with_extern_imported_global_size() {
        check(
            r#"
                #- main.capy

                other :: #import("other.capy");

                main :: () {
                    my_array : [other.size] bool = bool.[];
                };

                #- other.capy

                size : usize : extern;
            "#,
            expect![[r#"
                main::main : () -> void
                main::other : file other
                other::size : usize
                other:
                main:
                  0 : file other
                  1 : file other
                  2 : usize
                  6 : [0]bool
                  7 : void
                  8 : () -> void
                  l0 : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::ArraySizeNotConst, 111..121, None)],
        );
    }

    #[test]
    fn array_ty_with_extern_global_through_regular_global_size() {
        // I'm testing multiple things at once here.
        check(
            r#"
                foo : usize : extern;

                bar :: foo;

                main :: () {
                    my_array : [bar] i32 = i32.[];
                };
            "#,
            expect![[r#"
                main::bar : usize
                main::foo : usize
                main::main : () -> void
                1 : usize
                2 : usize
                6 : [0]i32
                7 : void
                8 : () -> void
                l0 : <unknown>
            "#]],
            |_| {
                [
                    (TyDiagnosticKind::GlobalNotConst, 63..66, None),
                    (TyDiagnosticKind::ArraySizeNotConst, 130..133, None),
                ]
            },
        );
    }

    #[test]
    fn array_ty_with_float_size() {
        check(
            r#"
                main :: () {
                    my_array : [1.0] i32 = i32.[1];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {float}
                4 : i32
                5 : [1]i32
                6 : void
                7 : () -> void
                l0 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(u8::MAX).into()),
                        found: Ty::Float(0).into(),
                    },
                    62..65,
                    None,
                )]
            },
        );
    }

    #[test]
    fn array_ty_with_local_size() {
        check(
            r#"
                main :: () {
                    size :: 4;

                    my_array : [size] i32 = i32.[1, 2, 3, 4];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : usize
                1 : usize
                5 : i32
                6 : i32
                7 : i32
                8 : i32
                9 : [4]i32
                10 : void
                11 : () -> void
                l0 : usize
                l1 : [4]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_ty_with_non_const_size() {
        check(
            r#"
                main :: () {
                    size := 3;

                    size = size + 1;

                    my_array : [size] i32 = i32.[1, 2, 3, 4];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : usize
                1 : usize
                2 : usize
                3 : usize
                4 : usize
                5 : usize
                9 : i32
                10 : i32
                11 : i32
                12 : i32
                13 : [4]i32
                14 : void
                15 : () -> void
                l0 : usize
                l1 : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::ArraySizeNotConst, 132..136, None)],
        );
    }

    #[test]
    fn array_ty_with_comptime_size() {
        check(
            r#"
                main :: () {
                    size :: comptime {
                        if true {
                            5
                        } else {
                            6
                        }
                    };

                    my_array : [size] i64 = i64.[1, 2, 3, 4, 5];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : bool
                1 : usize
                2 : usize
                3 : usize
                4 : usize
                5 : usize
                6 : usize
                7 : usize
                8 : usize
                12 : i64
                13 : i64
                14 : i64
                15 : i64
                16 : i64
                17 : [5]i64
                18 : void
                19 : () -> void
                l0 : usize
                l1 : [5]i64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_ty_with_negative_size() {
        check(
            r#"
                main :: () {
                    my_array : [-3] i32 = i32.[];
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {int}
                1 : {int}
                5 : [0]i32
                6 : void
                7 : () -> void
                l0 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(u8::MAX).into()),
                        found: Ty::IInt(0).into(),
                    },
                    62..64,
                    None,
                )]
            },
        );
    }

    #[test]
    fn index() {
        check(
            r#"
                main :: () -> i32 {
                    my_array := i32.[4, 8, 15, 16, 23, 42];

                    my_array[2]
                };
            "#,
            expect![[r#"
                main::main : () -> i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : [6]i32
                9 : [6]i32
                10 : usize
                11 : i32
                12 : i32
                13 : () -> i32
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn index_too_large() {
        check(
            r#"
                main :: () -> i32 {
                    my_array := i32.[4, 8, 15, 16, 23, 42];

                    my_array[1000]
                };
            "#,
            expect![[r#"
                main::main : () -> i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : [6]i32
                9 : [6]i32
                10 : usize
                11 : i32
                12 : i32
                13 : () -> i32
                l0 : [6]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexOutOfBounds {
                        index: 1000,
                        actual_size: 6,
                        array_ty: Ty::Array {
                            anonymous: false,
                            size: 6,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    },
                    118..132,
                    None,
                )]
            },
        );
    }

    #[test]
    fn inference_complex_by_annotation() {
        check(
            r#"
                main :: () {
                    num: i16 = {
                        res := 23;
                        if true {
                            res
                        } else {
                            -42
                        }
                    };
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i16
                2 : bool
                3 : i16
                4 : i16
                5 : i16
                6 : i16
                7 : i16
                8 : i16
                9 : i16
                10 : void
                11 : () -> void
                l0 : i16
                l1 : i16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_simple_by_return() {
        check(
            r#"
                main :: () -> usize {
                    num1 := 5;
                    num2 := num1;
                    num2
                };
            "#,
            expect![[r#"
                main::main : () -> usize
                1 : usize
                2 : usize
                3 : usize
                4 : usize
                5 : () -> usize
                l0 : usize
                l1 : usize
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_complex_by_return_ok() {
        check(
            r#"
                main :: () -> i8 {
                    num := {
                        res := 23;
                        if true {
                            res
                        } else {
                            -42
                        }
                    };
                    num
                };
            "#,
            expect![[r#"
                main::main : () -> i8
                1 : i8
                2 : bool
                3 : i8
                4 : i8
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : i8
                11 : i8
                12 : () -> i8
                l0 : i8
                l1 : i8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_complex_by_return_err() {
        check(
            r#"
                main :: () -> u8 {
                    num := {
                        res := 23;
                        if true {
                            res
                        } else {
                            -42
                        }
                    };
                    num
                };
            "#,
            expect![[r#"
                main::main : () -> u8
                1 : {int}
                2 : bool
                3 : {int}
                4 : {int}
                5 : {int}
                6 : {int}
                7 : {int}
                8 : {int}
                9 : {int}
                10 : {int}
                11 : {int}
                12 : () -> u8
                l0 : {int}
                l1 : {int}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                        found: Ty::IInt(0).into(),
                    },
                    34..321,
                    Some((TyDiagnosticHelpKind::TailExprReturnsHere, 300..303)),
                )]
            },
        );
    }

    #[test]
    fn function_with_params() {
        check(
            r#"
                add :: (x: i32, y: i32) -> i32 { x + y };
            "#,
            expect![[r#"
                main::add : (i32, i32) -> i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : (i32, i32) -> i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_definition_and_usage() {
        check(
            r#"
                main :: () {
                    a := 10;
                    a;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : void
                3 : () -> void
                l0 : {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_shadowing() {
        check(
            r#"
                foo :: () {
                    a := 10;
                    a := "10";
                    a;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : str
                2 : str
                3 : void
                4 : () -> void
                l0 : {uint}
                l1 : str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign() {
        check(
            r#"
                foo :: () {
                    a := "Hello";
                    a = "World"; // `a` on the left is an expression, and it's type is evaluated
                    a;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : str
                1 : str
                2 : str
                3 : str
                4 : void
                5 : () -> void
                l0 : str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_auto_small_to_big_same_sign() {
        check(
            r#"
                foo :: () -> i16 {
                    small: i8 = 42;
                    big: i16 = small;
                    big
                };
            "#,
            expect![[r#"
                main::foo : () -> i16
                2 : i8
                4 : i8
                5 : i16
                6 : i16
                7 : () -> i16
                l0 : i8
                l1 : i16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_auto_big_to_small_same_sign() {
        check(
            r#"
                foo :: () -> u8 {
                    big: u16 = 42;
                    small: u8 = big;
                    small
                };
            "#,
            expect![[r#"
                main::foo : () -> u8
                2 : u16
                4 : u16
                5 : u8
                6 : u8
                7 : () -> u8
                l0 : u16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                        found: Ty::UInt(16).into(),
                    },
                    102..105,
                    None,
                )]
            },
        );
    }

    #[test]
    fn local_auto_small_unsigned_to_big_signed() {
        check(
            r#"
                foo :: () -> i16 {
                    small: u8 = 42;
                    big: i16 = small;
                    big
                };
            "#,
            expect![[r#"
                main::foo : () -> i16
                2 : u8
                4 : u8
                5 : i16
                6 : i16
                7 : () -> i16
                l0 : u8
                l1 : i16
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_auto_small_signed_to_big_unsigned() {
        check(
            r#"
                foo :: () -> u16 {
                    small: i8 = 42;
                    big: u16 = small;
                    big
                };
            "#,
            expect![[r#"
                main::foo : () -> u16
                2 : i8
                4 : i8
                5 : u16
                6 : u16
                7 : () -> u16
                l0 : i8
                l1 : u16
            "#]],
            |_| {
                // should fail due to loss of sign
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(16).into()),
                        found: Ty::IInt(8).into(),
                    },
                    103..108,
                    None,
                )]
            },
        );
    }

    #[test]
    fn local_auto_signed_to_unsigned() {
        check(
            r#"
                foo :: () -> u16 {
                    sign: i16 = 42;
                    nada: u16 = sign;
                    nada
                };
            "#,
            expect![[r#"
                main::foo : () -> u16
                2 : i16
                4 : i16
                5 : u16
                6 : u16
                7 : () -> u16
                l0 : i16
                l1 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(16).into()),
                        found: Ty::IInt(16).into(),
                    },
                    104..108,
                    None,
                )]
            },
        );
    }

    #[test]
    fn local_auto_big_signed_to_small_unsigned() {
        check(
            r#"
                foo :: () -> u8 {
                    big: i16 = 42;
                    small: u8 = big;
                    small
                };
            "#,
            expect![[r#"
                main::foo : () -> u8
                2 : i16
                4 : i16
                5 : u8
                6 : u8
                7 : () -> u8
                l0 : i16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                        found: Ty::IInt(16).into(),
                    },
                    102..105,
                    None,
                )]
            },
        );
    }

    #[test]
    fn non_int_binary_expr() {
        check(
            r#"
                sum :: () -> i32 { "foo" + 1 };
            "#,
            expect![[r#"
                main::sum : () -> i32
                1 : str
                2 : i32
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: Ty::String.into(),
                        second: Ty::UInt(0).into(),
                    },
                    36..45,
                    None,
                )]
            },
        );
    }

    #[test]
    fn binary_expr_with_missing_operand() {
        check(
            r#"
                f :: () -> i32 { 5 + };
            "#,
            expect![[r#"
                main::f : () -> i32
                1 : i32
                2 : <unknown>
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn invalid_binary_expr_with_missing_operand() {
        check(
            r#"
                f :: () -> str { "hello" + };
            "#,
            expect![[r#"
                main::f : () -> str
                1 : str
                2 : <unknown>
                3 : str
                4 : str
                5 : () -> str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn invalid_num_cmp_binary_expr() {
        check(
            r#"
                f :: () -> bool { true < 5 };
            "#,
            expect![[r#"
                main::f : () -> bool
                1 : bool
                2 : {uint}
                3 : bool
                4 : bool
                5 : () -> bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Lt,
                        first: Ty::Bool.into(),
                        second: Ty::UInt(0).into(),
                    },
                    35..43,
                    None,
                )]
            },
        );
    }

    #[test]
    fn invalid_bool_cmp_binary_expr() {
        check(
            r#"
                f :: () -> bool { "hello" && "world" };
            "#,
            expect![[r#"
                main::f : () -> bool
                1 : str
                2 : str
                3 : bool
                4 : bool
                5 : () -> bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::LAnd,
                        first: Ty::String.into(),
                        second: Ty::String.into(),
                    },
                    35..53,
                    None,
                )]
            },
        );
    }

    #[test]
    fn bool_binary_expr() {
        check(
            r#"
                both :: () -> bool { true && false };
            "#,
            expect![[r#"
                main::both : () -> bool
                1 : bool
                2 : bool
                3 : bool
                4 : bool
                5 : () -> bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn bool_binary_expr_with_missing_operand() {
        check(
            r#"
                either :: () -> bool { true || };
            "#,
            expect![[r#"
                main::either : () -> bool
                1 : bool
                2 : <unknown>
                3 : bool
                4 : bool
                5 : () -> bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cmp_binary_expr() {
        check(
            r#"
                less :: () -> bool { 5 <= 10 };
            "#,
            expect![[r#"
                main::less : () -> bool
                1 : {uint}
                2 : {uint}
                3 : bool
                4 : bool
                5 : () -> bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cmp_binary_expr_with_missing_operands() {
        check(
            r#"
                equality :: () -> bool { 42 == };
            "#,
            expect![[r#"
                main::equality : () -> bool
                1 : {uint}
                2 : <unknown>
                3 : bool
                4 : bool
                5 : () -> bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn pos_unary_expr() {
        check(
            r#"
                redundant :: () -> u8 { +4 };
            "#,
            expect![[r#"
                main::redundant : () -> u8
                1 : u8
                2 : u8
                3 : u8
                4 : () -> u8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn neg_unary_expr() {
        check(
            r#"
                neg :: () -> u8 { -4 };
            "#,
            expect![[r#"
                main::neg : () -> u8
                1 : {int}
                2 : {int}
                3 : {int}
                4 : () -> u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                        found: Ty::IInt(0).into(),
                    },
                    33..39,
                    Some((TyDiagnosticHelpKind::TailExprReturnsHere, 35..37)),
                )]
            },
        );
    }

    #[test]
    fn multi_neg_unary_expr() {
        check(
            r#"
                pos :: () -> i8 { ----4 };
            "#,
            expect![[r#"
                main::pos : () -> i8
                1 : i8
                2 : i8
                3 : i8
                4 : i8
                5 : i8
                6 : i8
                7 : () -> i8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn bang_unary_expr() {
        check(
            r#"
                not :: () -> bool { !true };
            "#,
            expect![[r#"
                main::not : () -> bool
                1 : bool
                2 : bool
                3 : bool
                4 : () -> bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_function_body() {
        check(
            r#"
                s :: () -> str { 92 };
            "#,
            expect![[r#"
                main::s : () -> str
                1 : {uint}
                2 : {uint}
                3 : () -> str
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::String.into()),
                        found: Ty::UInt(0).into(),
                    },
                    32..38,
                    Some((TyDiagnosticHelpKind::TailExprReturnsHere, 34..36)),
                )]
            },
        );
    }

    #[test]
    fn call_void_function() {
        check(
            r#"
                main :: () { nothing(); };
                nothing :: () {};
            "#,
            expect![[r#"
                main::main : () -> void
                main::nothing : () -> void
                0 : () -> void
                1 : void
                2 : void
                3 : () -> void
                4 : void
                5 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn call_function_with_return_ty() {
        check(
            r#"
                main :: () -> i32 { number() };
                number :: () -> i32 { 5 };
            "#,
            expect![[r#"
                main::main : () -> i32
                main::number : () -> i32
                1 : () -> i32
                2 : i32
                3 : i32
                4 : () -> i32
                6 : i32
                7 : i32
                8 : () -> i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn call_function_with_params() {
        check(
            r#"
                main :: () -> i32 { id(10) };
                id :: (n: i32) -> i32 { n };
            "#,
            expect![[r#"
                main::id : (i32) -> i32
                main::main : () -> i32
                1 : (i32) -> i32
                2 : i32
                3 : i32
                4 : i32
                5 : () -> i32
                8 : i32
                9 : i32
                10 : (i32) -> i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_param_tys() {
        check(
            r#"
                main :: () -> i32 { multiply({}, "a") };
                multiply :: (x: i32, y: i32) -> i32 { x * y };
            "#,
            expect![[r#"
                main::main : () -> i32
                main::multiply : (i32, i32) -> i32
                1 : (i32, i32) -> i32
                2 : void
                3 : str
                4 : i32
                5 : i32
                6 : () -> i32
                10 : i32
                11 : i32
                12 : i32
                13 : i32
                14 : (i32, i32) -> i32
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                            found: Ty::Void.into(),
                        },
                        46..48,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                            found: Ty::String.into(),
                        },
                        50..53,
                        None,
                    ),
                ]
            },
        );
    }

    #[test]
    fn call_function_from_other_file() {
        check(
            r#"
                #- main.capy
                a :: () -> str {
                    greetings := #import("greetings.capy");

                    greetings.informal(10)
                };
                #- greetings.capy
                informal :: (n: i32) -> str { "Hello!" };
            "#,
            expect![[r#"
                greetings::informal : (i32) -> str
                main::a : () -> str
                greetings:
                  2 : str
                  3 : str
                  4 : (i32) -> str
                main:
                  1 : file greetings
                  2 : file greetings
                  3 : (i32) -> str
                  4 : i32
                  5 : str
                  6 : str
                  7 : () -> str
                  l0 : file greetings
            "#]],
            |_| [],
        );
    }

    #[test]
    fn attach_mismatch_diagnostics_to_block_tail_expr() {
        check(
            r#"
                main :: () {
                    take_i32({
                        a := 10 + 10;
                        "foo"
                    });
                };

                take_i32 :: (n: i32) {};
            "#,
            expect![[r#"
                main::main : () -> void
                main::take_i32 : (i32) -> void
                0 : (i32) -> void
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : str
                5 : str
                6 : void
                7 : void
                8 : () -> void
                10 : void
                11 : (i32) -> void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::String.into(),
                    },
                    59..150,
                    Some((TyDiagnosticHelpKind::TailExprReturnsHere, 123..128)),
                )]
            },
        );
    }

    #[test]
    fn distinct_int_mismatch() {
        check(
            r#"
                imaginary : type : distinct i32;

                main :: () -> i32 {
                    i : imaginary = 1;

                    i
                };
            "#,
            expect![[r#"
                main::imaginary : type
                main::main : () -> i32
                2 : type
                5 : main::imaginary
                6 : main::imaginary
                7 : main::imaginary
                8 : () -> i32
                l0 : main::imaginary
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::Distinct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    },
                    85..166,
                    Some((TyDiagnosticHelpKind::TailExprReturnsHere, 147..148)),
                )]
            },
        );
    }

    #[test]
    fn distinct_int_binary_weak_int() {
        check(
            r#"
                imaginary : type : distinct i32;

                main :: () -> imaginary {
                    i : imaginary = 1;

                    i + 2
                };
            "#,
            expect![[r#"
                main::imaginary : type
                main::main : () -> main::imaginary
                2 : type
                5 : main::imaginary
                6 : main::imaginary
                7 : main::imaginary
                8 : main::imaginary
                9 : main::imaginary
                10 : () -> main::imaginary
                l0 : main::imaginary
            "#]],
            |_| [],
        );
    }

    #[test]
    fn distinct_int_binary_itself() {
        check(
            r#"
                imaginary : type : distinct i32;

                main :: () -> imaginary {
                    i : imaginary = 1;

                    i + i
                };
            "#,
            expect![[r#"
                main::imaginary : type
                main::main : () -> main::imaginary
                2 : type
                5 : main::imaginary
                6 : main::imaginary
                7 : main::imaginary
                8 : main::imaginary
                9 : main::imaginary
                10 : () -> main::imaginary
                l0 : main::imaginary
            "#]],
            |_| [],
        );
    }

    #[test]
    fn distinct_int_binary_strong_int() {
        check(
            r#"
                imaginary : type : distinct i32;

                main :: () -> imaginary {
                    i : imaginary = 1;
                    x : i32 = 1;

                    i + x
                };
            "#,
            expect![[r#"
                main::imaginary : type
                main::main : () -> main::imaginary
                2 : type
                5 : main::imaginary
                7 : i32
                8 : main::imaginary
                9 : i32
                10 : main::imaginary
                11 : main::imaginary
                12 : () -> main::imaginary
                l0 : main::imaginary
                l1 : i32
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: Ty::Distinct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                        second: Ty::IInt(32).into(),
                    },
                    186..191,
                    None,
                )]
            },
        );
    }

    #[test]
    fn distinct_int_binary_other_distinct() {
        check(
            r#"
                imaginary : type : distinct i32;
                extra_imaginary : type : distinct i32;

                main :: () -> imaginary {
                    i : imaginary = 1;
                    x : extra_imaginary = 1;

                    i + x
                };
            "#,
            expect![[r#"
                main::extra_imaginary : type
                main::imaginary : type
                main::main : () -> main::imaginary
                2 : type
                5 : type
                8 : main::imaginary
                10 : main::extra_imaginary
                11 : main::imaginary
                12 : main::extra_imaginary
                13 : main::imaginary
                14 : main::imaginary
                15 : () -> main::imaginary
                l0 : main::imaginary
                l1 : main::extra_imaginary
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: Ty::Distinct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                        second: Ty::Distinct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("extra_imaginary")),
                            }),
                            uid: 1,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    },
                    253..258,
                    None,
                )]
            },
        );
    }

    #[test]
    fn distinct_pointers() {
        check(
            r#"
                something_far_away :: distinct ^i32;

                main :: () -> i32 {
                    i : something_far_away = ^1;

                    (^i32).(i)^
                };
            "#,
            expect![[r#"
                main::main : () -> i32
                main::something_far_away : type
                2 : type
                5 : i32
                6 : main::something_far_away
                7 : main::something_far_away
                11 : ^i32
                12 : i32
                13 : i32
                14 : () -> i32
                l0 : main::something_far_away
            "#]],
            |_| [],
        );
    }

    #[test]
    fn distinct_pointers_to_distinct_tys() {
        check(
            r#"
                imaginary :: distinct i32;
                imaginary_far_away :: distinct ^imaginary;

                main :: () -> imaginary {
                    i : imaginary = 1;

                    x : imaginary_far_away = ^i;

                    (^imaginary).(x)^
                };
            "#,
            expect![[r#"
                main::imaginary : type
                main::imaginary_far_away : type
                main::main : () -> main::imaginary
                1 : type
                4 : type
                7 : main::imaginary
                9 : main::imaginary
                10 : main::imaginary_far_away
                11 : main::imaginary_far_away
                15 : ^main::imaginary
                16 : main::imaginary
                17 : main::imaginary
                18 : () -> main::imaginary
                l0 : main::imaginary
                l1 : main::imaginary_far_away
            "#]],
            |_| [],
        );
    }

    #[test]
    fn distinct_arrays() {
        check(
            r#"
                Vector3 :: distinct [3] i32;

                main :: () {
                    my_point : Vector3 = i32.[4, 8, 15];

                    x := my_point[0];
                    y := my_point[1];
                    z := my_point[2];
                };
            "#,
            expect![[r#"
                main::Vector3 : type
                main::main : () -> void
                0 : usize
                3 : type
                6 : i32
                7 : i32
                8 : i32
                9 : [3]i32
                10 : main::Vector3
                11 : usize
                12 : i32
                13 : main::Vector3
                14 : usize
                15 : i32
                16 : main::Vector3
                17 : usize
                18 : i32
                19 : void
                20 : () -> void
                l0 : main::Vector3
                l1 : i32
                l2 : i32
                l3 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn ref_infer() {
        check(
            r#"
                main :: () -> ^i32 {
                    x := 42;

                    ^x
                };
            "#,
            expect![[r#"
                main::main : () -> ^i32
                2 : i32
                3 : i32
                4 : ^i32
                5 : ^i32
                6 : () -> ^i32
                l0 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn depend_depend_depend() {
        // while this may seem dumb, it was a bug when first changing hir_ty to be iterative.
        check(
            r#"
                foo :: 5;

                bar :: comptime foo;

                baz :: comptime bar;

                qux :: comptime baz;

                quux :: comptime qux;

                corge :: comptime quux;

                grault :: comptime corge;

                garply :: comptime grault;

                waldo :: comptime garply;

                fred :: comptime waldo;

                plugh :: comptime fred;

                xyzzy :: comptime plugh;

                thud :: comptime xyzzy;
            "#,
            expect![[r#"
                main::bar : i32
                main::baz : i32
                main::corge : i32
                main::foo : i32
                main::fred : i32
                main::garply : i32
                main::grault : i32
                main::plugh : i32
                main::quux : i32
                main::qux : i32
                main::thud : i32
                main::waldo : i32
                main::xyzzy : i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : i32
                9 : i32
                10 : i32
                11 : i32
                12 : i32
                13 : i32
                14 : i32
                15 : i32
                16 : i32
                17 : i32
                18 : i32
                19 : i32
                20 : i32
                21 : i32
                22 : i32
                23 : i32
                24 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn recursive_definitions() {
        check(
            r#"
                foo :: comptime bar;

                bar :: comptime foo;
            "#,
            expect![[r#"
                main::bar : <unknown>
                main::foo : <unknown>
                0 : <unknown>
                1 : <unknown>
                2 : <unknown>
                3 : <unknown>
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("bar")),
                        },
                    },
                    33..36,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_definitions_ty() {
        // the reason these tests were changed:
        //    tests::get_const_on_cyclic_globals
        //    tests::recursive_definitions
        //    tests::recursive_definitions_ty
        // is because `topo` now uses rustc-hash = "2.1"
        // and this changed the order in which things are evaluated.
        // possibly topo should use something order-preserving instead of
        // rustc-hash
        check(
            r#"
                foo : i32 : comptime bar;

                bar : i32 : comptime foo;
            "#,
            expect![[r#"
                main::bar : i32
                main::foo : i32
                1 : <unknown>
                2 : <unknown>
                4 : i32
                5 : i32
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("bar")),
                        },
                    },
                    38..41,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_param_ty() {
        check(
            r#"
                foo :: (bar: foo) {};
            "#,
            expect![[r#"
                main::foo : (<unknown>) -> void
                1 : void
                2 : (<unknown>) -> void
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("foo")),
                        },
                    },
                    30..33,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_global_ty_annotation() {
        check(
            r#"
                foo : foo : 5;
            "#,
            expect![[r#"
                main::foo : <unknown>
                1 : {uint}
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("foo")),
                        },
                    },
                    23..26,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_local_ty_annotation() {
        // this is handled in hir lowering
        check(
            r#"
                foo :: () {
                    a : a = 5;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : {uint}
                2 : void
                3 : () -> void
                l0 : <unknown>
            "#]],
            |_| [],
        );
    }

    #[test]
    fn recursive_struct() {
        // this is handled in hir lowering
        check(
            r#"
                Foo :: struct {
                    bar: Foo,
                };
            "#,
            expect![[r#"
                main::Foo : type
                1 : type
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("Foo")),
                        },
                    },
                    58..61,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_struct_and_multiple_literals() {
        // this is handled in hir lowering
        check(
            r#"
                Foo :: struct {
                    bar: Foo,
                };

                global_foo :: comptime {
                    Foo.{ bar = 0 }
                };

                main :: () {
                    my_foo := Foo.{
                        bar = true,
                    };
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::global_foo : main::Foo
                main::main : () -> void
                1 : type
                3 : {uint}
                4 : main::Foo
                5 : main::Foo
                6 : main::Foo
                8 : bool
                9 : main::Foo
                10 : void
                11 : () -> void
                l0 : main::Foo
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("Foo")),
                        },
                    },
                    58..61,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_distinct() {
        // this is handled in hir lowering
        check(
            r#"
                Foo :: distinct Foo;
            "#,
            expect![[r#"
                main::Foo : type
                1 : type
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("Foo")),
                        },
                    },
                    33..36,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_distinct_and_multiple_instances() {
        // this is handled in hir lowering
        check(
            r#"
                Foo :: distinct Foo;

                global_foo : Foo : comptime {
                    0
                };

                main :: () {
                    my_foo : Foo = 0;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::global_foo : main::Foo
                main::main : () -> void
                1 : type
                3 : {uint}
                4 : {uint}
                5 : {uint}
                7 : {uint}
                8 : void
                9 : () -> void
                l0 : main::Foo
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("Foo")),
                        },
                    },
                    33..36,
                    None,
                )]
            },
        );
    }

    #[test]
    fn recursive_array() {
        check(
            r#"
                a :: [0] a;
                b : a : 0;
            "#,
            expect![[r#"
                main::a : type
                main::b : [0]<unknown>
                0 : usize
                2 : type
                4 : {uint}
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("a")),
                        },
                    },
                    26..27,
                    None,
                )]
            },
        );
    }

    #[test]
    fn assign_var() {
        check(
            r#"
                main :: () {
                    foo := 5;

                    foo = 42;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : void
                4 : () -> void
                l0 : {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_binding() {
        check(
            r#"
                main :: () {
                    foo :: 5;

                    foo = 42;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : void
                4 : () -> void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    81..90,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 50..59)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_immutable_ref() {
        check(
            r#"
                main :: () {
                    foo := 5;
                    bar :: ^foo; 

                    bar^ = 42;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^{uint}
                4 : {uint}
                5 : {uint}
                6 : void
                7 : () -> void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    115..125,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 87..91)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_ref() {
        check(
            r#"
                main :: () {
                    foo := 5;
                    bar :: ^mut foo; 

                    bar^ = 42;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : ^mut {uint}
                4 : {uint}
                5 : {uint}
                6 : void
                7 : () -> void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_binary_expr() {
        check(
            r#"
                main :: () {
                    2 + 2 = 5;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : void
                5 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    50..60,
                    Some((TyDiagnosticHelpKind::FoundToBeImmutable, 50..55)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_ref_expr() {
        check(
            r#"
                main :: () {
                    {^mut 2}^ = 5;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : ^mut {uint}
                2 : ^mut {uint}
                3 : {uint}
                4 : {uint}
                5 : void
                6 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    51..57,
                    Some((TyDiagnosticHelpKind::FoundToBeImmutable, 56..57)),
                )]
            },
        );
    }

    #[test]
    fn mut_ref_to_binding() {
        check(
            r#"
                main :: () {
                    foo :: 5;
                    bar :: ^mut foo; 
                };
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : void
                4 : () -> void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    87..95,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 50..59)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_struct_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                foo :: () {
                    bob := Person.{
                        name = "Bob",
                        age = 26,
                    };

                    bob.age = bob.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                2 : type
                4 : str
                5 : i32
                6 : main::Person
                7 : main::Person
                8 : i32
                9 : main::Person
                10 : i32
                11 : i32
                12 : i32
                13 : void
                14 : () -> void
                l0 : main::Person
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_immutable_struct_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                foo :: () {
                    bob :: Person.{
                        name = "Bob",
                        age = 26,
                    };

                    bob.age = bob.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                2 : type
                4 : str
                5 : i32
                6 : main::Person
                7 : main::Person
                8 : i32
                9 : main::Person
                10 : i32
                11 : i32
                12 : i32
                13 : void
                14 : () -> void
                l0 : main::Person
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    296..318,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 164..274)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_struct_array_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                Company :: struct {
                    employees: [3]Person,
                };

                foo :: () {
                    my_company := Company.{
                        employees = Person.[
                            Person.{
                                name = "Bob",
                                age = 26,
                            },
                            Person.{
                                name = "Kyle",
                                age = 30,
                            },
                            Person.{
                                name = "John",
                                age = 23,
                            }
                        ],
                    };

                    my_company.employees[1].age = my_company.employees[1].age + 1;
                }
            "#,
            expect![[r#"
                main::Company : type
                main::Person : type
                main::foo : () -> void
                2 : type
                3 : usize
                6 : type
                10 : str
                11 : i32
                12 : main::Person
                14 : str
                15 : i32
                16 : main::Person
                18 : str
                19 : i32
                20 : main::Person
                21 : [3]main::Person
                22 : main::Company
                23 : main::Company
                24 : [3]main::Person
                25 : usize
                26 : main::Person
                27 : i32
                28 : main::Company
                29 : [3]main::Person
                30 : usize
                31 : main::Person
                32 : i32
                33 : i32
                34 : i32
                35 : void
                36 : () -> void
                l0 : main::Company
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_immutable_struct_array_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                Company :: struct {
                    employees: [3]Person,
                };

                foo :: () {
                    my_company :: Company.{
                        employees = Person.[
                            Person.{
                                name = "Bob",
                                age = 26,
                            },
                            Person.{
                                name = "Kyle",
                                age = 30,
                            },
                            Person.{
                                name = "John",
                                age = 23,
                            }
                        ],
                    };

                    my_company.employees[1].age = my_company.employees[1].age + 1;
                }
            "#,
            expect![[r#"
                main::Company : type
                main::Person : type
                main::foo : () -> void
                2 : type
                3 : usize
                6 : type
                10 : str
                11 : i32
                12 : main::Person
                14 : str
                15 : i32
                16 : main::Person
                18 : str
                19 : i32
                20 : main::Person
                21 : [3]main::Person
                22 : main::Company
                23 : main::Company
                24 : [3]main::Person
                25 : usize
                26 : main::Person
                27 : i32
                28 : main::Company
                29 : [3]main::Person
                30 : usize
                31 : main::Person
                32 : i32
                33 : i32
                34 : i32
                35 : void
                36 : () -> void
                l0 : main::Company
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    871..933,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 262..849)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_struct_immutable_ref_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                Ref_To_Person :: struct {
                    person: ^Person,
                };

                foo :: () {
                    ref :: Ref_To_Person.{
                        person = ^Person.{
                            name = "Bob",
                            age = 26,
                        },
                    };

                    ref.person^.age = ref.person^.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::Ref_To_Person : type
                main::foo : () -> void
                2 : type
                5 : type
                8 : str
                9 : i32
                10 : main::Person
                11 : ^main::Person
                12 : main::Ref_To_Person
                13 : main::Ref_To_Person
                14 : ^main::Person
                15 : main::Person
                16 : i32
                17 : main::Ref_To_Person
                18 : ^main::Person
                19 : main::Person
                20 : i32
                21 : i32
                22 : i32
                23 : void
                24 : () -> void
                l0 : main::Ref_To_Person
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    480..518,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 484..490)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_struct_mut_ref_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                Ref_To_Person :: struct {
                    person: ^mut Person,
                };

                foo :: () {
                    ref :: Ref_To_Person.{
                        person = ^mut Person.{
                            name = "Bob",
                            age = 26,
                        },
                    };

                    ref.person^.age = ref.person^.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::Ref_To_Person : type
                main::foo : () -> void
                2 : type
                5 : type
                8 : str
                9 : i32
                10 : main::Person
                11 : ^mut main::Person
                12 : main::Ref_To_Person
                13 : main::Ref_To_Person
                14 : ^mut main::Person
                15 : main::Person
                16 : i32
                17 : main::Ref_To_Person
                18 : ^mut main::Person
                19 : main::Person
                20 : i32
                21 : i32
                22 : i32
                23 : void
                24 : () -> void
                l0 : main::Ref_To_Person
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_mut_array() {
        check(
            r#"
                foo :: () {
                    array := i32.[1, 2, 3];

                    array[0] = 100;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : usize
                7 : i32
                8 : i32
                9 : void
                10 : () -> void
                l0 : [3]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_immutable_array() {
        check(
            r#"
                foo :: () {
                    array :: i32.[1, 2, 3];

                    array[0] = 100;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : usize
                7 : i32
                8 : {uint}
                9 : void
                10 : () -> void
                l0 : [3]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    94..109,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 49..72)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_param() {
        check(
            r#"
                foo :: (x: i32) {
                    x = 5;
                }
            "#,
            expect![[r#"
                main::foo : (i32) -> void
                1 : i32
                2 : {uint}
                3 : void
                4 : (i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    55..61,
                    Some((
                        TyDiagnosticHelpKind::ImmutableParam { assignment: true },
                        25..31,
                    )),
                )]
            },
        );
    }

    #[test]
    fn ref_to_param_ref() {
        check(
            r#"
                foo :: (x: ^i32) {
                    ^x;
                }
            "#,
            expect![[r#"
                main::foo : (^i32) -> void
                2 : ^i32
                3 : ^^i32
                4 : void
                5 : (^i32) -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mut_ref_to_param_ref() {
        check(
            r#"
                foo :: (x: ^i32) {
                    ^mut x;
                }
            "#,
            expect![[r#"
                main::foo : (^i32) -> void
                2 : ^i32
                3 : ^mut ^i32
                4 : void
                5 : (^i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    56..62,
                    Some((
                        TyDiagnosticHelpKind::ImmutableParam { assignment: false },
                        25..32,
                    )),
                )]
            },
        );
    }

    #[test]
    fn mut_ref_to_param_mut_ref() {
        check(
            r#"
                foo :: (x: ^mut i32) {
                    ^mut x;
                }
            "#,
            expect![[r#"
                main::foo : (^mut i32) -> void
                2 : ^mut i32
                3 : ^mut ^mut i32
                4 : void
                5 : (^mut i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    60..66,
                    Some((
                        TyDiagnosticHelpKind::ImmutableParam { assignment: false },
                        25..36,
                    )),
                )]
            },
        );
    }

    #[test]
    fn assign_to_param_array() {
        check(
            r#"
                foo :: (array: [3]i32) {
                    array[0] = 5;
                }
            "#,
            expect![[r#"
                main::foo : ([3]i32) -> void
                0 : usize
                3 : [3]i32
                4 : usize
                5 : i32
                6 : {uint}
                7 : void
                8 : ([3]i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    62..75,
                    Some((
                        TyDiagnosticHelpKind::ImmutableParam { assignment: true },
                        25..38,
                    )),
                )]
            },
        );
    }

    #[test]
    fn assign_to_param_immutable_ref() {
        check(
            r#"
                foo :: (bruh: ^i32) {
                    bruh^ = 5;
                }
            "#,
            expect![[r#"
                main::foo : (^i32) -> void
                2 : ^i32
                3 : i32
                4 : {uint}
                5 : void
                6 : (^i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    59..69,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 25..35)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_param_mut_ref() {
        check(
            r#"
                foo :: (array: ^mut i32) {
                    array^ = 5;
                }
            "#,
            expect![[r#"
                main::foo : (^mut i32) -> void
                2 : ^mut i32
                3 : i32
                4 : i32
                5 : void
                6 : (^mut i32) -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_param_immutable_ref_no_deref() {
        check(
            r#"
                foo :: (bruh: ^i32) {
                    bruh = 5;
                }
            "#,
            expect![[r#"
                main::foo : (^i32) -> void
                2 : ^i32
                3 : {uint}
                4 : void
                5 : (^i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    59..68,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 25..35)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_param_mut_ref_no_deref() {
        check(
            r#"
                foo :: (bruh: ^mut i32) {
                    bruh = 5;
                }
            "#,
            expect![[r#"
                main::foo : (^mut i32) -> void
                2 : ^mut i32
                3 : {uint}
                4 : void
                5 : (^mut i32) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    63..72,
                    Some((TyDiagnosticHelpKind::NotMutatingRefThroughDeref, 63..67)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_global() {
        check(
            r#"
                foo :: 5;

                bar :: () {
                    foo = 5;
                }
            "#,
            expect![[r#"
                main::bar : () -> void
                main::foo : i32
                0 : i32
                1 : i32
                2 : {uint}
                3 : void
                4 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    76..84,
                    Some((TyDiagnosticHelpKind::ImmutableGlobal, 17..26)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_global_in_other_file() {
        check(
            r#"
                #- main.capy
                other_file :: #import("other_file.capy");

                func :: () {
                    other_file.foo = 25;
                }
                #- other_file.capy
                foo :: 5;
            "#,
            expect![[r#"
                main::func : () -> void
                main::other_file : file other_file
                other_file::foo : i32
                other_file:
                  0 : i32
                main:
                  0 : file other_file
                  1 : file other_file
                  2 : i32
                  3 : {uint}
                  4 : void
                  5 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    108..128,
                    Some((TyDiagnosticHelpKind::ImmutableGlobal, 119..122)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_immutable_ref_binding_no_deref() {
        check(
            r#"
                foo :: () {
                    bar :: 5;

                    baz :: ^bar;

                    baz = 25;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^{uint}
                4 : {uint}
                5 : void
                6 : () -> void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    114..123,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 80..92)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_ref_binding_no_deref() {
        check(
            r#"
                foo :: () {
                    bar := 5;

                    baz :: ^mut bar;

                    baz = 25;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : ^mut {uint}
                4 : {uint}
                5 : void
                6 : () -> void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    118..127,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 80..96)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_immutable_ref_variable_no_deref() {
        check(
            r#"
                foo :: () {
                    val_a :: 5;
                    ptr_a := ^val_a;

                    val_b :: 42;
                    ptr_b :: ^val_b;

                    ptr_a = ptr_b;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : {uint}
                4 : {uint}
                5 : ^{uint}
                6 : ^{uint}
                7 : ^{uint}
                8 : void
                9 : () -> void
                l0 : {uint}
                l1 : ^{uint}
                l2 : {uint}
                l3 : ^{uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_mut_ref_varibale_no_deref() {
        check(
            r#"
                foo :: () {
                    val_a := 5;
                    ptr_a := ^mut val_a;

                    val_b := 42;
                    ptr_b :: ^mut val_b;

                    ptr_a = ptr_b;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : {uint}
                4 : {uint}
                5 : ^mut {uint}
                6 : ^mut {uint}
                7 : ^mut {uint}
                8 : void
                9 : () -> void
                l0 : {uint}
                l1 : ^mut {uint}
                l2 : {uint}
                l3 : ^mut {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mut_ref_to_immutable_ref() {
        check(
            r#"
                foo :: () {
                    bar := 5;

                    baz :: ^bar;

                    ^mut baz;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^{uint}
                4 : ^mut ^{uint}
                5 : void
                6 : () -> void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    114..122,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 80..92)),
                )]
            },
        );
    }

    #[test]
    fn mut_ref_to_mut_ref_binding() {
        check(
            r#"
                foo :: () {
                    bar := 5;

                    baz :: ^mut bar;

                    ^mut baz;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : ^mut {uint}
                4 : ^mut ^mut {uint}
                5 : void
                6 : () -> void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    118..126,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 80..96)),
                )]
            },
        );
    }

    #[test]
    fn reinfer_usages() {
        check(
            r#"
                main :: () {
                    foo := 5;
                
                    baz := foo;
                
                    foo = foo + 1;
                
                    bar(foo);
                };
                
                bar :: (x: usize) {};
            "#,
            expect![[r#"
                main::bar : (usize) -> void
                main::main : () -> void
                0 : usize
                1 : usize
                2 : usize
                3 : usize
                4 : usize
                5 : usize
                6 : (usize) -> void
                7 : usize
                8 : void
                9 : void
                10 : () -> void
                12 : void
                13 : (usize) -> void
                l0 : usize
                l1 : usize
            "#]],
            |_| [],
        );
    }

    #[test]
    fn pass_mut_ref_to_immutable_ref() {
        check(
            r#"
                main :: () {
                    foo := 5;
                
                    bar(^mut foo);
                };
                
                bar :: (x: ^i32) {};
            "#,
            expect![[r#"
                main::bar : (^i32) -> void
                main::main : () -> void
                0 : i32
                1 : (^i32) -> void
                2 : i32
                3 : ^mut i32
                4 : void
                5 : void
                6 : () -> void
                9 : void
                10 : (^i32) -> void
                l0 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn pass_immutable_ref_to_mut_ref() {
        check(
            r#"
                main :: () {
                    foo := 5;
                
                    bar(^foo);
                };
                
                bar :: (x: ^mut i32) {};
            "#,
            expect![[r#"
                main::bar : (^mut i32) -> void
                main::main : () -> void
                0 : {uint}
                1 : (^mut i32) -> void
                2 : {uint}
                3 : ^{uint}
                4 : void
                5 : void
                6 : () -> void
                9 : void
                10 : (^mut i32) -> void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Pointer {
                                mutable: true,
                                sub_ty: Ty::IInt(32).into(),
                            }
                            .into(),
                        ),
                        found: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    },
                    101..105,
                    None,
                )]
            },
        );
    }

    #[test]
    fn fn_with_ty_annotation_ok() {
        check(
            r#"
                foo : (arg: i32) -> void : (x: i32) {
                    // do stuff
                };
            "#,
            expect![[r#"
                main::foo : (i32) -> void
                5 : void
                6 : (i32) -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn fn_with_diff_fn_annotation() {
        check(
            r#"
                foo : (arg: f32, arg2: i8) -> str : (x: i32) {
                    foo(x);
                };
            "#,
            expect![[r#"
                main::foo : (f32, i8) -> str
                6 : (f32, i8) -> str
                7 : i32
                8 : str
                9 : void
                10 : (i32) -> void
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(
                                Ty::Function {
                                    param_tys: vec![
                                        ParamTy {
                                            ty: *ty::F32,
                                            varargs: false,
                                            impossible_to_differentiate: false,
                                        },
                                        ParamTy {
                                            ty: *ty::I8,
                                            varargs: false,
                                            impossible_to_differentiate: false,
                                        },
                                    ],
                                    return_ty: Ty::String.into(),
                                }
                                .into(),
                            ),
                            found: Ty::Function {
                                param_tys: vec![ParamTy {
                                    ty: *ty::I32,
                                    varargs: false,
                                    impossible_to_differentiate: false,
                                }],
                                return_ty: Ty::Void.into(),
                            }
                            .into(),
                        },
                        53..109,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(*ty::F32),
                            found: *ty::I32,
                        },
                        88..89,
                        None,
                    ),
                    (
                        TyDiagnosticKind::MissingArg {
                            expected: ExpectedTy::Concrete(Ty::IInt(8).into()),
                        },
                        89..89,
                        None,
                    ),
                ]
            },
        );
    }

    #[test]
    fn fn_with_global_annotation() {
        check(
            r#"
                foo : i32 : (x: i32) {
                    foo(x);
                }
            "#,
            expect![[r#"
                main::foo : i32
                2 : i32
                3 : i32
                4 : <unknown>
                5 : void
                6 : (i32) -> void
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(*ty::I32),
                            found: Ty::Function {
                                param_tys: vec![ParamTy {
                                    ty: *ty::I32,
                                    varargs: false,
                                    impossible_to_differentiate: false,
                                }],
                                return_ty: Ty::Void.into(),
                            }
                            .into(),
                        },
                        29..85,
                        None,
                    ),
                    (
                        TyDiagnosticKind::CalledNonFunction { found: *ty::I32 },
                        60..66,
                        None,
                    ),
                ]
            },
        );
    }

    #[test]
    fn missing_else() {
        check(
            r#"
                foo :: (arg: bool) -> str {
                    if arg {
                        "hello"
                    }
                };
            "#,
            expect![[r#"
                main::foo : (bool) -> str
                2 : bool
                3 : str
                4 : str
                5 : str
                6 : str
                7 : (bool) -> str
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MissingElse {
                        expected: Ty::String.into(),
                    },
                    65..127,
                    Some((
                        TyDiagnosticHelpKind::IfReturnsTypeHere {
                            found: Ty::String.into(),
                        },
                        98..105,
                    )),
                )]
            },
        );
    }

    #[test]
    fn local_ty_def() {
        check(
            r#"
                foo :: () {
                    imaginary :: distinct i32;

                    my_num : imaginary = 5;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                3 : distinct'0 i32
                4 : void
                5 : () -> void
                l0 : type
                l1 : distinct'0 i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_ty_mut() {
        check(
            r#"
                foo :: () {
                    imaginary := distinct i32;

                    my_num : imaginary = 5;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                3 : {uint}
                4 : void
                5 : () -> void
                l0 : type
                l1 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::LocalTyIsMutable,
                    106..115,
                    Some((TyDiagnosticHelpKind::MutableVariable, 49..75)),
                )]
            },
        );
    }

    #[test]
    fn local_ty_mut_through_binding() {
        check(
            r#"
                foo :: () {
                    imaginary := distinct i32;

                    binding :: imaginary;

                    my_num : binding = 5;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                2 : type
                4 : {uint}
                5 : void
                6 : () -> void
                l0 : type
                l1 : type
                l2 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::LocalTyIsMutable,
                    108..117,
                    Some((TyDiagnosticHelpKind::MutableVariable, 49..75)),
                )]
            },
        );
    }

    #[test]
    fn int_too_large_for_type() {
        check(
            r#"
                foo :: () {
                    my_num : i8 = 128;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i8
                2 : void
                3 : () -> void
                l0 : i8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IntTooBigForType {
                        found: 128,
                        max: 127,
                        ty: Ty::IInt(8).into(),
                    },
                    63..66,
                    None,
                )]
            },
        );
    }

    #[test]
    fn int_too_large_for_type_by_inference() {
        check(
            r#"
                foo :: () {
                    my_num := 128;

                    my_other_num : i8 = my_num;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : i8
                2 : i8
                3 : void
                4 : () -> void
                l0 : i8
                l1 : i8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IntTooBigForType {
                        found: 128,
                        max: 127,
                        ty: Ty::IInt(8).into(),
                    },
                    59..62,
                    None,
                )]
            },
        );
    }

    #[test]
    fn inference_by_too_large_for_u32() {
        check(
            r#"
                foo :: () {
                    my_num := 4_294_967_296;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : u64
                1 : void
                2 : () -> void
                l0 : u64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_by_too_large_for_i32() {
        check(
            r#"
                foo :: () {
                    my_num := -2_147_483_648;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : i64
                1 : i64
                2 : void
                3 : () -> void
                l0 : i64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn struct_literal() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                foo :: () {
                    some_guy := Person.{
                        name = "Joe Schmoe",
                        age = 31,
                    };
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                2 : type
                4 : str
                5 : i32
                6 : main::Person
                7 : void
                8 : () -> void
                l0 : main::Person
            "#]],
            |_| [],
        );
    }

    #[test]
    fn struct_literal_wrong_fields() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                foo :: () {
                    some_guy := Person.{
                        name = false,
                        height = "5'9\""
                    };
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                2 : type
                4 : bool
                5 : str
                6 : main::Person
                7 : void
                8 : () -> void
                l0 : main::Person
            "#]],
            |i| {
                let person_ty = Ty::Struct {
                    anonymous: false,
                    fqn: Some(hir::Fqn {
                        file: hir::FileName(i.intern("main.capy")),
                        name: hir::Name(i.intern("Person")),
                    }),
                    uid: 0,
                    members: vec![
                        MemberTy {
                            name: hir::Name(i.intern("name")),
                            ty: Ty::String.into(),
                        },
                        MemberTy {
                            name: hir::Name(i.intern("age")),
                            ty: Ty::IInt(32).into(),
                        },
                    ],
                }
                .into();

                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(Ty::String.into()),
                            found: Ty::Bool.into(),
                        },
                        216..221,
                        None,
                    ),
                    (
                        TyDiagnosticKind::NonExistentMember {
                            member: i.intern("height"),
                            found_ty: person_ty,
                        },
                        247..253,
                        None,
                    ),
                    (
                        TyDiagnosticKind::StructLiteralMissingMember {
                            member: i.intern("age"),
                            expected_ty: person_ty,
                        },
                        176..285,
                        None,
                    ),
                ]
            },
        );
    }

    #[test]
    fn get_struct_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                foo :: () -> i32 {
                    some_guy := Person.{
                        name = "Joe Schmoe",
                        age = 31,
                    };

                    some_guy.age
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> i32
                2 : type
                5 : str
                6 : i32
                7 : main::Person
                8 : main::Person
                9 : i32
                10 : i32
                11 : () -> i32
                l0 : main::Person
            "#]],
            |_| [],
        );
    }

    #[test]
    fn non_existent_field() {
        check(
            r#"
                Person :: struct {
                    name: str,
                    age: i32
                };

                foo :: () -> i32 {
                    some_guy := Person.{
                        name = "Joe Schmoe",
                        age = 31,
                    };

                    some_guy.height
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> i32
                2 : type
                5 : str
                6 : i32
                7 : main::Person
                8 : main::Person
                9 : <unknown>
                10 : <unknown>
                11 : () -> i32
                l0 : main::Person
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NonExistentMember {
                        member: i.intern("height"),
                        found_ty: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Person")),
                            }),
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("name")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("age")),
                                    ty: Ty::IInt(32).into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    315..330,
                    None,
                )]
            },
        );
    }

    #[test]
    fn if_mismatch() {
        check(
            r#"
                foo :: (bar: bool) -> bool {
                    // this evaluates to `<unknown>`, so the function's return type isn't checked
                    if bar {
                        "Hello!"
                    } else {
                        100
                    }
                }
            "#,
            expect![[r#"
                main::foo : (bool) -> bool
                2 : bool
                3 : str
                4 : str
                5 : {uint}
                6 : {uint}
                7 : <unknown>
                8 : <unknown>
                9 : (bool) -> bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IfMismatch {
                        first: Ty::String.into(),
                        second: Ty::UInt(0).into(),
                    },
                    164..284,
                    None,
                )]
            },
        );
    }

    #[test]
    fn index_non_array() {
        check(
            r#"
                foo :: () {
                    bar := "Hello!";

                    bar[0];
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : str
                1 : str
                2 : usize
                3 : <unknown>
                4 : void
                5 : () -> void
                l0 : str
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexNonArray {
                        found: Ty::String.into(),
                    },
                    87..93,
                    None,
                )]
            },
        );
    }

    #[test]
    fn extra_arg() {
        // todo: since there are two extra args here, maybe throw two errors instead of one
        check(
            r#"
                bar :: (num: i32) {};

                foo :: () {
                    bar(1, 2, 3);
                }
            "#,
            expect![[r#"
                main::bar : (i32) -> void
                main::foo : () -> void
                1 : void
                2 : (i32) -> void
                3 : (i32) -> void
                4 : i32
                5 : {uint}
                6 : {uint}
                7 : void
                8 : void
                9 : () -> void
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::ExtraArg {
                            found: Ty::UInt(0).into(),
                        },
                        95..96,
                        None,
                    ),
                    (
                        TyDiagnosticKind::ExtraArg {
                            found: Ty::UInt(0).into(),
                        },
                        98..99,
                        None,
                    ),
                ]
            },
        );
    }

    #[test]
    fn missing_arg() {
        check(
            r#"
                bar :: (num: i32, text: str, condition: bool) {};

                foo :: () {
                    bar(1, "hello");
                }
            "#,
            expect![[r#"
                main::bar : (i32, str, bool) -> void
                main::foo : () -> void
                3 : void
                4 : (i32, str, bool) -> void
                5 : (i32, str, bool) -> void
                6 : i32
                7 : str
                8 : void
                9 : void
                10 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MissingArg {
                        expected: ExpectedTy::Concrete(Ty::Bool.into()),
                    },
                    130..130,
                    None,
                )]
            },
        );
    }

    #[test]
    fn varargs() {
        check(
            r#"
                bar :: (numbers: ...i8) {};

                foo :: () {
                    bar(1, 2, 3, 4, 5);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8) -> void
                main::foo : () -> void
                1 : void
                2 : (...[]i8) -> void
                3 : (...[]i8) -> void
                4 : i8
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : void
                10 : void
                11 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn multiple_varargs() {
        check(
            r#"
                bar :: (numbers: ...i8, conditions: ...bool, text: ...str, more_numbers: ...i8) {};

                foo :: () {
                    bar(1, 2, 3, 4, 5, true, false, "hello", "world", "sailor", "wassup", 42);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
                main::foo : () -> void
                4 : void
                5 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
                6 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
                7 : i8
                8 : i8
                9 : i8
                10 : i8
                11 : i8
                12 : bool
                13 : bool
                14 : str
                15 : str
                16 : str
                17 : str
                18 : i8
                19 : void
                20 : void
                21 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn multiple_varargs_with_regular_args() {
        check(
            r#"
                bar :: (numbers: ...i8, a: str, conditions: ...bool, b: str, text: ...str, c: i8, more_numbers: ...i8) {};

                foo :: () {
                    bar(1, 2, 3, 4, 5, "conditions: ", true, false, "text: ", "hello", "world", "sailor", "wassup", 0, 42);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
                main::foo : () -> void
                7 : void
                8 : (...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
                9 : (...[]i8, str, ...[]bool, str, ...[]str, i8, ...[]i8) -> void
                10 : i8
                11 : i8
                12 : i8
                13 : i8
                14 : i8
                15 : str
                16 : bool
                17 : bool
                18 : str
                19 : str
                20 : str
                21 : str
                22 : str
                23 : i8
                24 : i8
                25 : void
                26 : void
                27 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn empty_varargs() {
        check(
            r#"
                bar :: (conditions: ...bool) {};

                foo :: () {
                    bar();
                }
            "#,
            expect![[r#"
                main::bar : (...[]bool) -> void
                main::foo : () -> void
                1 : void
                2 : (...[]bool) -> void
                3 : (...[]bool) -> void
                4 : void
                5 : void
                6 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn multiple_empty_varargs() {
        check(
            r#"
                bar :: (numbers: ...i8, conditions: ...bool, text: ...str, more_numbers: ...i8) {};

                foo :: () {
                    bar();
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
                main::foo : () -> void
                4 : void
                5 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
                6 : (...[]i8, ...[]bool, ...[]str, ...[]i8) -> void
                7 : void
                8 : void
                9 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn multiple_empty_varargs_one_regular_arg_diff_than_previous() {
        check(
            r#"
                bar :: (numbers: ...i8, conditions: ...bool, regular_arg: str, text: ...str, more_numbers: ...i8) {};

                foo :: () {
                    bar("will this go to the regular arg?");
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
                main::foo : () -> void
                5 : void
                6 : (...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
                7 : (...[]i8, ...[]bool, str, ...[]str, ...[]i8) -> void
                8 : str
                9 : void
                10 : void
                11 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn multiple_empty_varargs_one_regular_arg_same_as_previous() {
        check(
            r#"
                bar :: (numbers: ...i8, conditions: ...bool, regular_arg: i64, text: ...str, more_numbers: ...i8) {};

                foo :: () {
                    bar(42);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
                main::foo : () -> void
                5 : void
                6 : (...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
                7 : (...[]i8, ...[]bool, i64, ...[]str, ...[]i8) -> void
                8 : i8
                9 : void
                10 : void
                11 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MissingArg {
                        expected: ExpectedTy::Concrete(Ty::IInt(64).into()),
                    },
                    174..174,
                    None,
                )]
            },
        );
    }

    #[test]
    fn impossible_to_differentiate_prev_varargs_next_arg() {
        check(
            r#"
                bar :: (first: ...i8, second: i64) {};

                foo :: () {
                    bar(1, 2, 3, 4, 5);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, i64) -> void
                main::foo : () -> void
                2 : void
                3 : (...[]i8, i64) -> void
                4 : (...[]i8, i64) -> void
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : void
                11 : void
                12 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                        previous_ty: Ty::IInt(8).into(),
                        current_ty: Ty::IInt(64).into(),
                    },
                    39..50,
                    None,
                )]
            },
        );
    }

    #[test]
    fn impossible_to_differentiate_prev_varargs_next_vararg() {
        check(
            r#"
                bar :: (first: ...i8, second: ...u64) {};

                foo :: () {
                    bar(1, 2, 3, 4, 5);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, ...[]u64) -> void
                main::foo : () -> void
                2 : void
                3 : (...[]i8, ...[]u64) -> void
                4 : (...[]i8, ...[]u64) -> void
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : void
                11 : void
                12 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                        previous_ty: Ty::IInt(8).into(),
                        current_ty: Ty::UInt(64).into(),
                    },
                    39..53,
                    None,
                )]
            },
        );
    }

    #[test]
    fn impossible_to_differentiate_prev_varargs_next_any_vararg() {
        check(
            r#"
                bar :: (first: ...i8, second: ...any) {};

                foo :: () {
                    bar(1, 2, 3, 4, 5);
                }
            "#,
            expect![[r#"
                main::bar : (...[]i8, ...[]any) -> void
                main::foo : () -> void
                2 : void
                3 : (...[]i8, ...[]any) -> void
                4 : (...[]i8, ...[]any) -> void
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : void
                11 : void
                12 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                        previous_ty: Ty::IInt(8).into(),
                        current_ty: Ty::Any.into(),
                    },
                    39..53,
                    None,
                )]
            },
        );
    }

    #[test]
    fn call_non_function() {
        check(
            r#"
                foo :: () {
                    wow := "Wow!";

                    wow(42);
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : str
                1 : str
                2 : {uint}
                3 : <unknown>
                4 : void
                5 : () -> void
                l0 : str
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CalledNonFunction {
                        found: Ty::String.into(),
                    },
                    85..92,
                    None,
                )]
            },
        );
    }

    #[test]
    fn deref_non_pointer() {
        check(
            r#"
                foo :: () {
                    wow := "Wow!";

                    wow^;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : str
                1 : str
                2 : <unknown>
                3 : void
                4 : () -> void
                l0 : str
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::DerefNonPointer {
                        found: Ty::String.into(),
                    },
                    85..89,
                    None,
                )]
            },
        );
    }

    #[test]
    fn param_as_ty() {
        check(
            r#"
                foo :: (T: type) {
                    wow : T = "hello :)";
                }
            "#,
            expect![[r#"
                main::foo : (type) -> void
                2 : str
                3 : void
                4 : (type) -> void
                l0 : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::ParamNotATy, 62..63, None)],
        );
    }

    #[test]
    fn cast_as_local_ty() {
        check(
            r#"
                foo :: () {
                    imaginary :: distinct i32;

                    real : i32 = 5;

                    imaginary.(real);
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                3 : i32
                4 : i32
                6 : distinct'0 i32
                7 : void
                8 : () -> void
                l0 : type
                l1 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn no_implicit_struct_cast() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: i8,
                };

                Bar :: struct {
                    a: i32,
                    b: i8,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = 2,
                    };

                    my_bar : Bar = my_foo;
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                2 : type
                5 : type
                8 : i32
                9 : i8
                10 : main::Foo
                12 : main::Foo
                13 : void
                14 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Struct {
                                anonymous: false,
                                fqn: Some(hir::Fqn {
                                    file: hir::FileName(i.intern("main.capy")),
                                    name: hir::Name(i.intern("Bar")),
                                }),
                                uid: 1,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("a")),
                                        ty: Ty::IInt(32).into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("b")),
                                        ty: Ty::IInt(8).into(),
                                    },
                                ],
                            }
                            .into(),
                        ),
                        found: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::IInt(8).into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    406..412,
                    None,
                )]
            },
        );
    }

    #[test]
    fn cast_struct_same_fields() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: i8,
                };

                Bar :: struct {
                    a: i32,
                    b: i8,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = 2,
                    };

                    my_bar : Bar = Bar.(my_foo);
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                2 : type
                5 : type
                8 : i32
                9 : i8
                10 : main::Foo
                12 : main::Foo
                14 : main::Bar
                15 : void
                16 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cast_struct_diff_field_order() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: i8,
                };

                Bar :: struct {
                    b: i8,
                    a: i32,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = 2,
                    };

                    my_bar : Bar = Bar.(my_foo);
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                2 : type
                5 : type
                8 : i32
                9 : i8
                10 : main::Foo
                12 : main::Foo
                14 : main::Bar
                15 : void
                16 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cast_struct_diff_field_ty_castable() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: i8,
                };

                Bar :: struct {
                    a: i32,
                    b: i16,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = 2,
                    };

                    my_bar : Bar = Bar.(my_foo);
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                2 : type
                5 : type
                8 : i32
                9 : i8
                10 : main::Foo
                12 : main::Foo
                14 : main::Bar
                15 : void
                16 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cast_struct_diff_field_ty_uncastable() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: [2]i32,
                };

                Bar :: struct {
                    a: i32,
                    b: [3]i32,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = .[2, 3],
                    };

                    my_bar : Bar = Bar.(my_foo);
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                1 : usize
                4 : type
                6 : usize
                9 : type
                12 : i32
                13 : i32
                14 : i32
                15 : [2]i32
                16 : main::Foo
                18 : main::Foo
                20 : main::Bar
                21 : void
                22 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::Array {
                                        anonymous: false,
                                        size: 2,
                                        sub_ty: Ty::IInt(32).into(),
                                    }
                                    .into(),
                                },
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::Array {
                                        anonymous: false,
                                        size: 3,
                                        sub_ty: Ty::IInt(32).into(),
                                    }
                                    .into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    420..432,
                    None,
                )]
            },
        );
    }

    #[test]
    fn cast_struct_diff_field_name() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: i8,
                };

                Bar :: struct {
                    x: i32,
                    y: i8,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = 2,
                    };

                    my_bar : Bar = Bar.(my_foo);
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                2 : type
                5 : type
                8 : i32
                9 : i8
                10 : main::Foo
                12 : main::Foo
                14 : main::Bar
                15 : void
                16 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::IInt(8).into(),
                                },
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("x")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("y")),
                                    ty: Ty::IInt(8).into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    406..418,
                    None,
                )]
            },
        );
    }

    #[test]
    fn cast_struct_diff_field_len() {
        check(
            r#"
                Foo :: struct {
                    a: i32,
                    b: i8,
                };

                Bar :: struct {
                    a: i32,
                    b: i8,
                    c: str,
                };

                main :: () {
                    my_foo : Foo = Foo.{
                        a = 1,
                        b = 2,
                    };

                    my_bar : Bar = Bar.(my_foo);
                };
            "#,
            expect![[r#"
                main::Bar : type
                main::Foo : type
                main::main : () -> void
                2 : type
                6 : type
                9 : i32
                10 : i8
                11 : main::Foo
                13 : main::Foo
                15 : main::Bar
                16 : void
                17 : () -> void
                l0 : main::Foo
                l1 : main::Bar
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::IInt(8).into(),
                                },
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            anonymous: false,
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::IInt(32).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::IInt(8).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("c")),
                                    ty: Ty::String.into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    434..446,
                    None,
                )]
            },
        );
    }

    #[test]
    fn lambda_ty_annotation() {
        check(
            r#"
                bar :: (s: str) {
                    // do stuff
                } 

                foo :: () {
                    a : (s: str) -> void = (s: str) {};

                    a = bar;

                    a("Hello!");
                }
            "#,
            expect![[r#"
                main::bar : (str) -> void
                main::foo : () -> void
                1 : void
                2 : (str) -> void
                8 : void
                9 : (str) -> void
                10 : (str) -> void
                11 : (str) -> void
                12 : (str) -> void
                13 : str
                14 : void
                15 : void
                16 : () -> void
                l0 : (str) -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn lambda_with_body_ty_annotation() {
        check(
            r#"
                foo :: () {
                    a : (s: str) -> void {} = (s: str) {};

                    a("Hello!");
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                5 : void
                6 : (str) -> void
                7 : <unknown>
                8 : str
                9 : <unknown>
                10 : void
                11 : () -> void
                l0 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Type.into()),
                        found: Ty::Function {
                            param_tys: vec![ParamTy {
                                ty: Ty::String.into(),
                                varargs: false,
                                impossible_to_differentiate: false,
                            }],
                            return_ty: Ty::Void.into(),
                        }
                        .into(),
                    },
                    53..72,
                    None,
                )]
            },
        );
    }

    #[test]
    fn lambda_ty_no_return() {
        // this is only to make sure that `is_safe_to_compile` works correctly.
        // this will panic if there's some error and `is_safe_to_compile`
        // returns true. since I know for a fact that the parser is going to throw an
        // error on the following input, and I know that the following did not panic,
        // it's safe to say that `is_safe_to_compile` returned false and
        // works correctly on this input.
        check(
            r#"
                foo :: () {
                    (a: i32, b: str);
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : <unknown>
                3 : (i32, str) -> void
                4 : void
                5 : () -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn comptime() {
        check(
            r#"
                foo :: () {
                    foo : str = comptime {
                        2 * 5
                    };
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : {uint}
                5 : {uint}
                6 : void
                7 : () -> void
                l0 : str
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Intern::new(Ty::String)),
                        found: Intern::new(Ty::UInt(0)),
                    },
                    61..123,
                    None,
                )]
            },
        );
    }

    #[test]
    fn comptime_pointer() {
        check(
            r#"
                foo :: () {
                    comptime {
                        x := 5;

                        ^x
                    };
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^{uint}
                4 : <unknown>
                5 : void
                6 : () -> void
                l0 : {uint}
            "#]],
            |_| [(TyDiagnosticKind::ComptimePointer, 49..141, None)],
        );
    }

    #[test]
    fn non_const_global() {
        check(
            r#"
                foo :: 2 + 2;
            "#,
            expect![[r#"
                main::foo : i32
                0 : i32
                1 : i32
                2 : i32
            "#]],
            |_| [(TyDiagnosticKind::GlobalNotConst, 24..29, None)],
        );
    }

    #[test]
    fn any_ptr() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;

                    ptr : ^i32 = ^foo;
                    ptr : rawptr = (rawptr).(ptr);
                    ptr : ^f32 = (^f32).(ptr);

                    foo : f32 = ptr^;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                4 : i32
                5 : ^i32
                7 : ^i32
                10 : rawptr
                13 : rawptr
                17 : ^f32
                19 : ^f32
                20 : f32
                21 : void
                22 : () -> void
                l0 : i32
                l1 : ^i32
                l2 : rawptr
                l3 : ^f32
                l4 : f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn any_slice() {
        check(
            r#"
                get_any :: () {
                    foo : [] i32 = i32.[100, 200];

                    ptr : rawslice = rawslice.(foo);

                    foo : [] f32 = []f32.(ptr);

                    first : f32 = foo[0];
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                3 : i32
                4 : i32
                5 : [2]i32
                7 : []i32
                9 : rawslice
                12 : rawslice
                15 : []f32
                17 : []f32
                18 : usize
                19 : f32
                20 : void
                21 : () -> void
                l0 : []i32
                l1 : rawslice
                l2 : []f32
                l3 : f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn cast_ptr_without_any() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;

                    ptr : ^i32 = ^foo;
                    ptr : ^f32 = (^f32).(ptr);

                    foo : f32 = ptr^;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                4 : i32
                5 : ^i32
                8 : ^i32
                12 : ^f32
                14 : ^f32
                15 : f32
                16 : void
                17 : () -> void
                l0 : i32
                l1 : ^i32
                l2 : ^f32
                l3 : f32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                        to: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Float(32).into(),
                        }
                        .into(),
                    },
                    141..153,
                    None,
                )]
            },
        );
    }

    #[test]
    fn cast_slice_without_any() {
        check(
            r#"
                get_any :: () {
                    foo : [] i32 = i32.[100, 200];

                    foo : [] f32 = []f32.(foo);
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                3 : i32
                4 : i32
                5 : [2]i32
                8 : []i32
                11 : []f32
                12 : void
                13 : () -> void
                l0 : []i32
                l1 : []f32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::Slice {
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                        to: Ty::Slice {
                            sub_ty: Ty::Float(32).into(),
                        }
                        .into(),
                    },
                    120..131,
                    None,
                )]
            },
        );
    }

    #[test]
    fn deref_rawptr() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;

                    ptr : ^i32 = ^foo;
                    ptr : rawptr = (rawptr).(ptr);

                    foo := ptr^;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                4 : i32
                5 : ^i32
                7 : ^i32
                10 : rawptr
                11 : rawptr
                12 : <unknown>
                13 : void
                14 : () -> void
                l0 : i32
                l1 : ^i32
                l2 : rawptr
                l3 : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::DerefRaw, 187..191, None)],
        );
    }

    #[test]
    fn index_rawslice() {
        check(
            r#"
                get_any :: () {
                    foo : [3] i32 = i32.[5, 10, 15];

                    ptr : [] i32 = foo;
                    ptr : rawslice = rawslice.(ptr);

                    foo := ptr[0];
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                0 : usize
                4 : i32
                5 : i32
                6 : i32
                7 : [3]i32
                10 : [3]i32
                12 : []i32
                14 : rawslice
                15 : rawslice
                16 : usize
                17 : <unknown>
                18 : void
                19 : () -> void
                l0 : [3]i32
                l1 : []i32
                l2 : rawslice
                l3 : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::IndexRaw { size: None }, 208..214, None)],
        );
    }

    // todo: should there be a rawarray type?
    // #[test]
    // fn index_any_array() {
    //     check(
    //         r#"
    //             get_any :: (foo: [3] any) {
    //                 foo : any = foo[0];
    //             }
    //         "#,
    //         expect![[r#"
    //             main::get_any : ([3]any) -> void
    //             0 : usize
    //             4 : [3]any
    //             5 : usize
    //             6 : <unknown>
    //             7 : void
    //             8 : ([3]any) -> void
    //             l0 : any
    //         "#]],
    //         |_| [(TyDiagnosticKind::IndexRaw { size: Some(3) }, 77..83, None)],
    //     );
    // }

    #[test]
    fn auto_real_ptr_to_any_ptr() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;
                    ptr : ^i32 = ^foo;

                    ptr : rawptr = ptr;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                4 : i32
                5 : ^i32
                7 : ^i32
                8 : void
                9 : () -> void
                l0 : i32
                l1 : ^i32
                l2 : rawptr
            "#]],
            |_| [],
        );
    }

    #[test]
    fn auto_any_ptr_to_real_ptr() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;
                    ptr : ^i32 = ^foo;
                    ptr : rawptr = ptr as rawptr;

                    ptr : ^i32 = ptr;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                4 : i32
                5 : ^i32
                7 : ^i32
                9 : rawptr
                12 : rawptr
                13 : void
                14 : () -> void
                l0 : i32
                l1 : ^i32
                l2 : rawptr
                l3 : ^i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Pointer {
                                mutable: false,
                                sub_ty: Ty::IInt(32).into(),
                            }
                            .into(),
                        ),
                        found: Ty::RawPtr { mutable: false }.into(),
                    },
                    191..194,
                    None,
                )]
            },
        );
    }

    #[test]
    fn auto_real_slice_to_rawslice() {
        check(
            r#"
                get_any :: () {
                    foo : [] i32 = i32.[5, 10, 15];

                    ptr : rawslice = foo;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                3 : i32
                4 : i32
                5 : i32
                6 : [3]i32
                8 : []i32
                9 : void
                10 : () -> void
                l0 : []i32
                l1 : rawslice
            "#]],
            |_| [],
        );
    }

    #[test]
    fn auto_rawslice_to_real_slice() {
        check(
            r#"
                get_any :: () {
                    foo : [] i32 = i32.[5, 10, 15];
                    ptr : rawslice = rawslice.(foo);

                    ptr : [] i32 = ptr;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                3 : i32
                4 : i32
                5 : i32
                6 : [3]i32
                8 : []i32
                10 : rawslice
                13 : rawslice
                14 : void
                15 : () -> void
                l0 : []i32
                l1 : rawslice
                l2 : []i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Slice {
                                sub_ty: Ty::IInt(32).into(),
                            }
                            .into(),
                        ),
                        found: Ty::RawSlice.into(),
                    },
                    174..177,
                    None,
                )]
            },
        );
    }

    #[test]
    fn any_ptr_to_str() {
        check(
            r#"
                get_any :: () {
                    data := char.['h', 'i', '\0'];
                    ptr := (rawptr).(^data);
                    str := str.(ptr);
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : char
                2 : char
                3 : char
                4 : [3]char
                5 : [3]char
                6 : ^[3]char
                9 : rawptr
                10 : rawptr
                12 : str
                13 : void
                14 : () -> void
                l0 : [3]char
                l1 : rawptr
                l2 : str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn char_ptr_to_str() {
        check(
            r#"
                get_any :: () {
                    data := char.['h', 'i', '\0'];
                    ptr := (^char).((rawptr).(^data));
                    str := str.(ptr);
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : char
                2 : char
                3 : char
                4 : [3]char
                5 : [3]char
                6 : ^[3]char
                9 : rawptr
                13 : ^char
                14 : ^char
                16 : str
                17 : void
                18 : () -> void
                l0 : [3]char
                l1 : ^char
                l2 : str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn u8_ptr_to_str() {
        check(
            r#"
                get_any :: () {
                    data := char.['h', 'i', '\0'];
                    ptr := (^u8).((rawptr).(^data));
                    str := str.(ptr);
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : char
                2 : char
                3 : char
                4 : [3]char
                5 : [3]char
                6 : ^[3]char
                9 : rawptr
                13 : ^u8
                14 : ^u8
                16 : str
                17 : void
                18 : () -> void
                l0 : [3]char
                l1 : ^u8
                l2 : str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn char_array_to_str() {
        check(
            r"
                get_any :: () {
                    data := char.['H', 'i', '\0'];
                    str := str.(data);
                }
            ",
            expect![[r#"
                main::get_any : () -> void
                1 : char
                2 : char
                3 : char
                4 : [3]char
                5 : [3]char
                7 : str
                8 : void
                9 : () -> void
                l0 : [3]char
                l1 : str
            "#]],
            |_| [],
        );
    }

    #[test]
    fn char() {
        check(
            r"
                foo :: () {
                    my_char := 'A';
                }
            ",
            expect![[r#"
                main::foo : () -> void
                0 : char
                1 : void
                2 : () -> void
                l0 : char
            "#]],
            |_| [],
        )
    }

    #[test]
    fn char_as_u8() {
        check(
            r"
                foo :: () {
                    my_char := 'A';
                    my_u8 := u8.(my_char);
                }
            ",
            expect![[r#"
                main::foo : () -> void
                0 : char
                1 : char
                3 : u8
                4 : void
                5 : () -> void
                l0 : char
                l1 : u8
            "#]],
            |_| [],
        )
    }

    #[test]
    fn no_implicit_char_to_u8() {
        check(
            r"
                foo :: () {
                    my_char := 'A';
                    my_u8 : u8 = my_char;
                }
            ",
            expect![[r#"
                main::foo : () -> void
                0 : char
                2 : char
                3 : void
                4 : () -> void
                l0 : char
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(8).into()),
                        found: Ty::Char.into(),
                    },
                    98..105,
                    None,
                )]
            },
        )
    }

    #[test]
    fn field_of_struct_ptr() {
        check(
            r#"
                Foo :: struct {
                    a: i32
                };

                main :: () {
                    my_foo := Foo.{
                        a = 25
                    };

                    ptr := ^my_foo;

                    ptr.a;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                1 : type
                3 : i32
                4 : main::Foo
                5 : main::Foo
                6 : ^main::Foo
                7 : ^main::Foo
                8 : i32
                9 : void
                10 : () -> void
                l0 : main::Foo
                l1 : ^main::Foo
            "#]],
            |_| [],
        );
    }

    #[test]
    fn field_of_struct_ptr_ptr() {
        check(
            r#"
                Foo :: struct {
                    a: i32
                };

                main :: () {
                    my_foo := Foo.{
                        a = 25
                    };

                    ptr := ^^my_foo;

                    ptr.a;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                1 : type
                3 : i32
                4 : main::Foo
                5 : main::Foo
                6 : ^main::Foo
                7 : ^^main::Foo
                8 : ^^main::Foo
                9 : i32
                10 : void
                11 : () -> void
                l0 : main::Foo
                l1 : ^^main::Foo
            "#]],
            |_| [],
        );
    }

    #[test]
    fn field_of_non_struct_ptr_ptr() {
        check(
            r#"
                main :: () {
                    my_foo := 5;

                    ptr := ^^my_foo;

                    ptr.a;
                }
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^^{uint}
                4 : ^^{uint}
                5 : <unknown>
                6 : void
                7 : () -> void
                l0 : {uint}
                l1 : ^^{uint}
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NonExistentMember {
                        member: i.intern("a"),
                        found_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Pointer {
                                mutable: false,
                                sub_ty: Ty::UInt(0).into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    122..127,
                    None,
                )]
            },
        );
    }

    #[test]
    fn non_existent_field_of_struct_ptr_ptr() {
        check(
            r#"
                Foo :: struct {
                    a: i32
                };

                main :: () {
                    my_foo := Foo.{
                        a = 25
                    };

                    ptr := ^^my_foo;

                    ptr.b;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                1 : type
                3 : i32
                4 : main::Foo
                5 : main::Foo
                6 : ^main::Foo
                7 : ^^main::Foo
                8 : ^^main::Foo
                9 : <unknown>
                10 : void
                11 : () -> void
                l0 : main::Foo
                l1 : ^^main::Foo
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NonExistentMember {
                        member: i.intern("b"),
                        found_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Pointer {
                                mutable: false,
                                sub_ty: Ty::Struct {
                                    anonymous: false,
                                    fqn: Some(hir::Fqn {
                                        file: hir::FileName(i.intern("main.capy")),
                                        name: hir::Name(i.intern("Foo")),
                                    }),
                                    uid: 0,
                                    members: vec![MemberTy {
                                        name: hir::Name(i.intern("a")),
                                        ty: Ty::IInt(32).into(),
                                    }],
                                }
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    258..263,
                    None,
                )]
            },
        );
    }

    #[test]
    fn mutate_field_of_struct_ptr_ptr() {
        check(
            r#"
                Foo :: struct {
                    a: i32
                };

                main :: () {
                    my_foo := Foo.{
                        a = 25
                    };

                    ptr := ^mut ^mut my_foo;

                    ptr.a = 5;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                1 : type
                3 : i32
                4 : main::Foo
                5 : main::Foo
                6 : ^mut main::Foo
                7 : ^mut ^mut main::Foo
                8 : ^mut ^mut main::Foo
                9 : i32
                10 : i32
                11 : void
                12 : () -> void
                l0 : main::Foo
                l1 : ^mut ^mut main::Foo
            "#]],
            |_| [],
        );
    }

    #[test]
    fn index_of_array_ptr() {
        check(
            r#"
                main :: () {
                    arr := i32.[1, 2, 3];

                    ptr := ^arr;

                    ptr[0];
                }
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : ^[3]i32
                7 : ^[3]i32
                8 : usize
                9 : i32
                10 : void
                11 : () -> void
                l0 : [3]i32
                l1 : ^[3]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn index_of_array_ptr_ptr() {
        check(
            r#"
                main :: () {
                    arr := i32.[1, 2, 3];

                    ptr := ^^arr;

                    ptr[0];
                }
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : ^[3]i32
                7 : ^^[3]i32
                8 : ^^[3]i32
                9 : usize
                10 : i32
                11 : void
                12 : () -> void
                l0 : [3]i32
                l1 : ^^[3]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn index_of_non_array_ptr_ptr() {
        check(
            r#"
                main :: () {
                    arr := 5;

                    ptr := ^^arr;

                    ptr[0];
                }
            "#,
            expect![[r#"
                main::main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^^{uint}
                4 : ^^{uint}
                5 : usize
                6 : <unknown>
                7 : void
                8 : () -> void
                l0 : {uint}
                l1 : ^^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexNonArray {
                        found: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Pointer {
                                mutable: false,
                                sub_ty: Ty::UInt(0).into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    116..122,
                    None,
                )]
            },
        );
    }

    #[test]
    fn index_too_large_of_array_ptr_ptr() {
        check(
            r#"
                main :: () {
                    arr := i32.[1, 2, 3];

                    ptr := ^^arr;

                    ptr[10];
                }
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : ^[3]i32
                7 : ^^[3]i32
                8 : ^^[3]i32
                9 : usize
                10 : i32
                11 : void
                12 : () -> void
                l0 : [3]i32
                l1 : ^^[3]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexOutOfBounds {
                        index: 10,
                        actual_size: 3,
                        array_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Pointer {
                                mutable: false,
                                sub_ty: Ty::Array {
                                    anonymous: false,
                                    size: 3,
                                    sub_ty: Ty::IInt(32).into(),
                                }
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    128..135,
                    None,
                )]
            },
        );
    }

    #[test]
    fn mutable_index_of_array_ptr_ptr() {
        check(
            r#"
                main :: () {
                    arr := i32.[1, 2, 3];

                    ptr :: ^mut ^mut arr;

                    ptr[1] = 50;
                }
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : ^mut [3]i32
                7 : ^mut ^mut [3]i32
                8 : ^mut ^mut [3]i32
                9 : usize
                10 : i32
                11 : i32
                12 : void
                13 : () -> void
                l0 : [3]i32
                l1 : ^mut ^mut [3]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn immutable_index_of_array_ptr_ptr() {
        check(
            r#"
                main :: () {
                    arr :: i32.[1, 2, 3];

                    ptr := ^^arr;

                    ptr[1] = 50;
                }
            "#,
            expect![[r#"
                main::main : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                6 : ^[3]i32
                7 : ^^[3]i32
                8 : ^^[3]i32
                9 : usize
                10 : i32
                11 : {uint}
                12 : void
                13 : () -> void
                l0 : [3]i32
                l1 : ^^[3]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    128..140,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 100..105)),
                )]
            },
        );
    }

    #[test]
    fn entry_point_void() {
        check_impl(
            r#"
                start :: () {};
            "#,
            expect![[r#"
                main::start : () -> void
                0 : void
                1 : () -> void
            "#]],
            |_| [],
            Some("start"),
        )
    }

    #[test]
    fn entry_point_int() {
        check_impl(
            r#"
                entry :: () -> i16 { 0 };
            "#,
            expect![[r#"
                main::entry : () -> i16
                1 : i16
                2 : i16
                3 : () -> i16
            "#]],
            |_| [],
            Some("entry"),
        )
    }

    #[test]
    fn entry_point_uint() {
        check_impl(
            r#"
                main :: () -> usize { 0 };
            "#,
            expect![[r#"
                main::main : () -> usize
                1 : usize
                2 : usize
                3 : () -> usize
            "#]],
            |_| [],
            Some("main"),
        )
    }

    #[test]
    fn entry_point_non_function() {
        check_impl(
            r#"
                main :: 5;
            "#,
            expect![[r#"
                main::main : i32
                0 : i32
            "#]],
            |_| [(TyDiagnosticKind::EntryNotFunction, 17..27, None)],
            Some("main"),
        )
    }

    #[test]
    fn entry_point_bad_params_and_return() {
        check_impl(
            r#"
                foo :: (x: i32, y: bool) -> str {
                    "Hello!"
                }
            "#,
            expect![[r#"
                main::foo : (i32, bool) -> str
                3 : str
                4 : str
                5 : (i32, bool) -> str
            "#]],
            |_| {
                [
                    (TyDiagnosticKind::EntryHasParams, 24..41, None),
                    (TyDiagnosticKind::EntryBadReturn, 45..48, None),
                ]
            },
            Some("foo"),
        )
    }

    #[test]
    fn array_of_local_ty() {
        check(
            r#"
                main :: () -> i32 {
                    int :: i32;
                    imaginary :: distinct int;
                    imaginary_vec3 :: distinct [3] imaginary;

                    arr : imaginary_vec3 = imaginary.[1, 2, 3];

                    i32.(arr[0])
                }
            "#,
            expect![[r#"
                main::main : () -> i32
                1 : type
                3 : type
                4 : usize
                7 : type
                10 : {uint}
                11 : {uint}
                12 : {uint}
                13 : [3]distinct'0 i32
                14 : distinct'1 [3]distinct'0 i32
                15 : usize
                16 : distinct'0 i32
                18 : i32
                19 : i32
                20 : () -> i32
                l0 : type
                l1 : type
                l2 : type
                l3 : distinct'1 [3]distinct'0 i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn struct_of_local_tys() {
        check(
            r#"
                main :: () -> i32 {
                    int :: i32;
                    imaginary :: distinct int;
                    complex :: struct {
                        real_part: int,
                        imaginary_part: imaginary,
                    };

                    my_complex := complex.{
                        real_part = 5,
                        imaginary_part = 42,
                    };

                    i32.(my_complex.real_part) + i32.(my_complex.imaginary_part)
                }
            "#,
            expect![[r#"
                main::main : () -> i32
                1 : type
                3 : type
                6 : type
                8 : i32
                9 : distinct'0 i32
                10 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
                11 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
                12 : i32
                14 : i32
                15 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
                16 : distinct'0 i32
                18 : i32
                19 : i32
                20 : i32
                21 : () -> i32
                l0 : type
                l1 : type
                l2 : type
                l3 : struct'1 {real_part: i32, imaginary_part: distinct'0 i32}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn lambda_with_local_ty() {
        check(
            r#"
                main :: () -> i32 {
                    int :: i32;
                    imaginary :: distinct int;
                    imaginary_vec3 :: distinct [3] imaginary;
                    complex :: struct {
                        real_part: int,
                        imaginary_part: imaginary,
                    };
                
                    my_complex := complex.{
                        real_part = 5,
                        imaginary_part = 42,
                    };
                
                    do_math :: (c: complex) -> imaginary_vec3 {
                        // this is kind of akward because while we can access locals
                        // in the parameters and return type, we can't access `imaginary`
                        // from inside the body of this lambda
                        // this could be alleviated by adding a `type_of` builtin
                        i32.[1, c.real_part * i32.(c.imaginary_part), 3]
                    };
                
                    i32.(do_math(my_complex)[1])
                }
            "#,
            expect![[r#"
                main::main : () -> i32
                1 : type
                3 : type
                4 : usize
                7 : type
                10 : type
                12 : i32
                13 : distinct'0 i32
                14 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                18 : i32
                19 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                20 : i32
                21 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                22 : distinct'0 i32
                24 : i32
                25 : i32
                26 : i32
                27 : [3]i32
                28 : [3]i32
                29 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
                30 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
                31 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                32 : distinct'1 [3]distinct'0 i32
                33 : usize
                34 : distinct'0 i32
                36 : i32
                37 : i32
                38 : () -> i32
                l0 : type
                l1 : type
                l2 : type
                l3 : type
                l4 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                l5 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_void_block_no_tail_match() {
        check(
            r#"
                foo :: () {
                    {
                        break;
                        break {};
                        break {};
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : void
                2 : void
                3 : void
                4 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_i32_block_no_tail_mismatch() {
        check(
            r#"
                foo :: () {
                    {
                        break 123;
                        break {};
                        break true;
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : void
                2 : bool
                3 : <unknown>
                4 : <unknown>
                5 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::UInt(0).into()),
                        found: Ty::Void.into(),
                    },
                    116..118,
                    Some((
                        TyDiagnosticHelpKind::BreakHere {
                            break_ty: Ty::UInt(0).into(),
                        },
                        75..85,
                    )),
                )]
            },
        )
    }

    #[test]
    fn paren_infer() {
        check(
            r#"
                foo :: () -> u16 {
                    (42 * (11 / 2))
                }
            "#,
            expect![[r#"
                main::foo : () -> u16
                1 : u16
                2 : u16
                3 : u16
                4 : u16
                5 : u16
                6 : u16
                7 : u16
                8 : u16
                9 : () -> u16
            "#]],
            |_| [],
        )
    }

    #[test]
    fn paren_spread() {
        check(
            r#"
                foo :: () {
                    x : i8 = 42;
                    (42 * ((2 >> x) / 2));
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i8
                2 : i8
                3 : i8
                4 : i8
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : i8
                11 : i8
                12 : void
                13 : () -> void
                l0 : i8
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_i32_block_tail_match() {
        check(
            r#"
                foo :: () -> i32 {
                    {
                        break 123;
                        42
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_void_block_tail_mismatch() {
        check(
            r#"
                foo :: () {
                    {
                        break {};
                        42
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : {uint}
                2 : <unknown>
                3 : <unknown>
                4 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Void.into()),
                        found: Ty::UInt(0).into(),
                    },
                    109..111,
                    Some((
                        TyDiagnosticHelpKind::BreakHere {
                            break_ty: Ty::Void.into(),
                        },
                        75..84,
                    )),
                )]
            },
        )
    }

    #[test]
    fn break_i32_block_from_inner() {
        check(
            r#"
                foo :: () {
                    `blk: {
                        {
                            break `blk {};
                        }

                        42
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : noeval
                2 : {uint}
                3 : <unknown>
                4 : <unknown>
                5 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Void.into()),
                        found: Ty::UInt(0).into(),
                    },
                    177..179,
                    Some((
                        TyDiagnosticHelpKind::BreakHere {
                            break_ty: Ty::Void.into(),
                        },
                        111..125,
                    )),
                )]
            },
        )
    }

    #[test]
    fn break_i32_block_from_inner_tail() {
        check(
            r#"
            foo :: () -> i32 {
                `blk: {
                    {
                        break `blk true;
                        break 5;
                        42
                    }
                }
            }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : bool
                2 : {uint}
                3 : {uint}
                4 : {uint}
                5 : <unknown>
                6 : <unknown>
                7 : () -> i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Bool.into()),
                        found: Ty::UInt(0).into(),
                    },
                    76..200,
                    Some((
                        TyDiagnosticHelpKind::BreakHere {
                            break_ty: Ty::Bool.into(),
                        },
                        102..118,
                    )),
                )]
            },
        )
    }

    #[test]
    fn break_unknown_label() {
        check(
            r#"
                foo :: () {
                    break `blk 42;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : noeval
                2 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn return_match() {
        check(
            r#"
                foo :: () -> i32 {
                    return 100;
                    42
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : i32
                2 : i32
                3 : i32
                4 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn return_mismatch() {
        check(
            r#"
                foo :: () -> i32 {
                    return "hello";
                    42
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : str
                2 : {uint}
                3 : <unknown>
                4 : () -> i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::String.into()),
                        found: Ty::UInt(0).into(),
                    },
                    92..94,
                    Some((
                        TyDiagnosticHelpKind::BreakHere {
                            break_ty: Ty::String.into(),
                        },
                        56..71,
                    )),
                )]
            },
        )
    }

    #[test]
    fn return_only() {
        check(
            r#"
                foo :: () -> i32 {
                    return 42;
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : i32
                2 : i32
                3 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn return_with_globals() {
        check(
            r#"
                a :: 42;
                b :: comptime a;
                c :: comptime b;
                d :: comptime c;

                foo :: () -> i32 {
                    return 42;
                    d;
                    return 5;
                }
            "#,
            expect![[r#"
                main::a : i32
                main::b : i32
                main::c : i32
                main::d : i32
                main::foo : () -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                8 : i32
                9 : i32
                10 : i32
                11 : i32
                12 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_loop() {
        check(
            r#"
                foo :: () {
                    `my_loop: loop {
                        break `my_loop;
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : noeval
                1 : void
                2 : void
                3 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_loop_with_value() {
        check(
            r#"
                foo :: () -> i32 {
                    `my_loop: loop {
                        break `my_loop 42;
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : i32
                2 : noeval
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_loop_with_multiple_values() {
        check(
            r#"
                foo :: () {
                    loop {
                        x : i16 = 42;
                        break x;

                        break 15;

                        x : i32 = 23;
                        break x;
                    };
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i16
                2 : i16
                3 : i16
                5 : i32
                6 : i32
                7 : noeval
                8 : i32
                9 : void
                10 : () -> void
                l0 : i16
                l1 : i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_while() {
        check(
            r#"
                foo :: () {
                    `my_loop: while 2 + 2 == 4 {
                        break `my_loop;
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : bool
                5 : noeval
                6 : void
                7 : void
                8 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_while_with_void() {
        check(
            r#"
                foo :: () {
                    `my_loop: while 2 + 2 == 4 {
                        break `my_loop {};
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : bool
                5 : void
                6 : noeval
                7 : void
                8 : void
                9 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_while_with_value() {
        check(
            r#"
                foo :: () {
                    `my_loop: while 2 + 2 == 4 {
                        break `my_loop 42;
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : bool
                5 : {uint}
                6 : noeval
                7 : <unknown>
                8 : <unknown>
                9 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Void.into()),
                        found: Ty::UInt(0).into(),
                    },
                    117..119,
                    None,
                )]
            },
        )
    }

    #[test]
    fn continue_works() {
        check(
            r#"
                foo :: () -> i32 {
                    loop {
                        continue;
                    }
                    42
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : noeval
                2 : void
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_inner_if_no_else() {
        check(
            r#"
                foo :: () -> i32 {
                    {
                        if true {
                            return 123;
                        }
                    }

                    0
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : bool
                2 : i32
                3 : noeval
                4 : void
                5 : void
                6 : i32
                7 : i32
                8 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_inner_if_with_else_no_break() {
        check(
            r#"
                foo :: () -> i32 {
                    {
                        if true {
                            return 123;
                        } else {

                        }
                    }

                    0
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : bool
                2 : i32
                3 : noeval
                4 : void
                5 : void
                6 : void
                7 : i32
                8 : i32
                9 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_inner_if_with_else_break() {
        check(
            r#"
                foo :: () -> i32 {
                    {
                        if true {
                            return 123;
                        } else {
                            return 456;
                        }
                    }

                    0
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : bool
                2 : i32
                3 : noeval
                4 : i32
                5 : noeval
                6 : noeval
                7 : noeval
                8 : i32
                9 : i32
                10 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn reinfer_break_usages() {
        check(
            r#"
                foo :: () {
                    {
                        x := 0;
                        break x;
                        y : i8 = x;
                    };
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : i8
                1 : i8
                3 : i8
                4 : i8
                5 : void
                6 : () -> void
                l0 : i8
                l1 : i8
            "#]],
            |_| [],
        )
    }

    #[test]
    fn implicit_weak_ptr_to_any() {
        check(
            r#"
                foo :: () {
                    x : rawptr = ^42;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : {uint}
                2 : ^{uint}
                3 : void
                4 : () -> void
                l0 : rawptr
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::RawPtr { mutable: false }.into()),
                        found: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    },
                    62..65,
                    None,
                )]
            },
        )
    }

    #[test]
    fn explicit_weak_ptr_to_i32_to_any() {
        check(
            r#"
                foo :: () {
                    x : rawptr = (^i32).(^42);
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i32
                2 : ^i32
                6 : ^i32
                7 : void
                8 : () -> void
                l0 : rawptr
            "#]],
            |_| [],
        )
    }

    #[test]
    fn slice() {
        check(
            r#"
                foo :: () {
                    x : [] i32 = i32.[1, 2, 3];

                    y : [] i32 = i32.[4, 6, 7, 8];
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                3 : i32
                4 : i32
                5 : i32
                6 : [3]i32
                10 : i32
                11 : i32
                12 : i32
                13 : i32
                14 : [4]i32
                15 : void
                16 : () -> void
                l0 : []i32
                l1 : []i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn explicit_slice_to_array() {
        check(
            r#"
                foo :: () {
                    x : [] i32 = i32.[1, 2, 3];
                    
                    y := [3]i32.(x);
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                3 : i32
                4 : i32
                5 : i32
                6 : [3]i32
                7 : []i32
                8 : usize
                11 : [3]i32
                12 : void
                13 : () -> void
                l0 : []i32
                l1 : [3]i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn implicit_slice_to_array() {
        check(
            r#"
                foo :: () {
                    x : [] i32 = i32.[1, 2, 3];
                    
                    y : [3] i32 = x;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                3 : i32
                4 : i32
                5 : i32
                6 : [3]i32
                7 : usize
                10 : []i32
                11 : void
                12 : () -> void
                l0 : []i32
                l1 : [3]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Array {
                                anonymous: false,
                                size: 3,
                                sub_ty: Ty::IInt(32).into(),
                            }
                            .into(),
                        ),
                        found: Ty::Slice {
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    },
                    132..133,
                    None,
                )]
            },
        )
    }

    #[test]
    fn explicit_array_to_slice() {
        check(
            r#"
                foo :: () {
                    x := i32.[1, 2, 3];
                    
                    y := []i32.(x);
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : [3]i32
                8 : []i32
                9 : void
                10 : () -> void
                l0 : [3]i32
                l1 : []i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn implicit_array_to_slice() {
        check(
            r#"
                foo :: () {
                    x : [3] i32 = i32.[1, 2, 3];
                    
                    y : [] i32 = x;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : usize
                4 : i32
                5 : i32
                6 : i32
                7 : [3]i32
                10 : [3]i32
                11 : void
                12 : () -> void
                l0 : [3]i32
                l1 : []i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn extern_function() {
        check(
            r#"
                foo :: (s: str) -> void extern;
            "#,
            expect![[r#"
                main::foo : (str) -> void
                3 : (str) -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn extern_global_with_type() {
        check(
            r#"
                foo : i32 : extern;
            "#,
            expect![[r#"
                main::foo : i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn extern_global_without_type() {
        check(
            r#"
                foo :: extern;
            "#,
            expect![[r#"
                main::foo : <unknown>
            "#]],
            |_| [(TyDiagnosticKind::ExternGlobalMissingTy, 17..31, None)],
        )
    }

    #[test]
    fn extern_global_reference() {
        // mainly just for checking `is_safe_to_compile`
        check(
            r#"
                #- main.capy
                other :: #import("other.capy");

                foo : i32 : extern;

                bar :: () {
                    foo;
                    other.baz;
                };
                #- other.capy
                baz : i32 : extern;
            "#,
            expect![[r#"
                main::bar : () -> void
                main::foo : i32
                main::other : file other
                other::baz : i32
                other:
                main:
                  0 : file other
                  2 : i32
                  3 : file other
                  4 : i32
                  5 : void
                  6 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn defers() {
        check(
            r#"
                foo :: () {
                    defer 5 + 5;
                    defer foo();
                    defer {
                        defer !true;
                    };
                    defer {
                        break "owo";
                    };
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : () -> void
                4 : void
                5 : bool
                6 : bool
                7 : void
                8 : str
                9 : str
                10 : void
                11 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn comptime_types() {
        check(
            r#"
                Foo :: comptime {
                    Bar :: comptime str;
                    Baz :: comptime i32;

                    struct {
                        a: Bar,
                        b : Baz,
                    }
                };

                run :: () {
                    my_foo := Foo.{
                        a = "hello",
                        b = 42,
                    };
                };
            "#,
            expect![[r#"
                main::Foo : type
                main::run : () -> void
                0 : type
                1 : type
                2 : type
                3 : type
                6 : type
                7 : type
                8 : type
                10 : str
                11 : i32
                12 : main::Foo
                13 : void
                14 : () -> void
                l0 : type
                l1 : type
                l2 : main::Foo
            "#]],
            |_| [],
        )
    }

    #[test]
    fn reinfer_params() {
        // usually an argument will replace the weak type of a variable.
        // in this case it doesn't and so more advanced replacing is needed.
        // todo: make sure the test is still testing for what it was testing for
        check(
            r#"
                accept_any :: (val: any) {}
                
                foo :: () {
                    x := 0;
                    accept_any(x);
                    i16.(x);
                }
            "#,
            expect![[r#"
                main::accept_any : (any) -> void
                main::foo : () -> void
                1 : void
                2 : (any) -> void
                3 : i16
                4 : (any) -> void
                5 : i16
                6 : void
                7 : i16
                9 : i16
                10 : void
                11 : () -> void
                l0 : i16
            "#]],
            |_| [],
        )
    }

    #[test]
    fn ty_ptr_becomes_ty() {
        check(
            r#"
                foo :: () {
                    x : type = ^i32;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                2 : type
                3 : void
                4 : () -> void
                l0 : type
            "#]],
            |_| [],
        )
    }

    #[test]
    fn array_literal_as_type() {
        // pre 2/6/2025:
        // this is just to make sure that the compiler doens't show a diagnostic
        // like "expected `type` but found `<unknown>`"

        // post 2/6/2025:
        // due to the changes in `parser`,
        // this is now parsed as:
        // ```text
        //  x : i32 = .[]
        // ```
        // which honestly makes more sense
        //
        // I added `int_literal_as_type` and `unknown_as_type` to try and check for the same thing
        // this test was checking for
        check(
            r#"
                foo :: () {
                    x : i32.[];
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : [0]~void
                2 : void
                3 : () -> void
                l0 : i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(32).into()),
                        found: Ty::Array {
                            anonymous: true,
                            size: 0,
                            sub_ty: Ty::Void.into(),
                        }
                        .into(),
                    },
                    56..59,
                    None,
                )]
            },
        )
    }

    #[test]
    fn int_literal_as_type() {
        check(
            r#"
                foo :: () {
                    x : 42;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : void
                2 : () -> void
                l0 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Type.into()),
                        found: Ty::UInt(0).into(),
                    },
                    53..55,
                    None,
                )]
            },
        )
    }

    #[test]
    fn unknown_as_type() {
        // this is just to make sure that the compiler doens't show a diagnostic
        // like "expected `type` but found `<unknown>`"
        check(
            r#"
                foo :: () {
                    x : _;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : void
                2 : () -> void
                l0 : <unknown>
            "#]],
            |_| [],
        )
    }

    #[test]
    fn default_value_i32() {
        check(
            r#"
                defaults :: () {
                    x : i32;
                }
            "#,
            expect![[r#"
                main::defaults : () -> void
                1 : void
                2 : () -> void
                l0 : i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn default_value_char_array() {
        check(
            r#"
                defaults :: () {
                    x : [10]char;
                }
            "#,
            expect![[r#"
                main::defaults : () -> void
                0 : usize
                3 : void
                4 : () -> void
                l0 : [10]char
            "#]],
            |_| [],
        )
    }

    #[test]
    fn default_value_distinct_distinct_struct_with_valid_types() {
        check(
            r#"
                defaults :: () {
                    x : distinct distinct struct {
                        a: [2][4]u8,
                        b: i16,
                        c: distinct f32,
                        d: bool,
                        e: char,
                        f: void,
                    };
                }
            "#,
            expect![[r#"
                main::defaults : () -> void
                0 : usize
                1 : usize
                14 : void
                15 : () -> void
                l0 : distinct'3 distinct'2 struct'1 {a: [2][4]u8, b: i16, c: distinct'0 f32, d: bool, e: char, f: void}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn default_value_i32_ptr() {
        check(
            r#"
                defaults :: () {
                    x : ^i32;
                }
            "#,
            expect![[r#"
                main::defaults : () -> void
                2 : void
                3 : () -> void
                l0 : ^i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::DeclTypeHasNoDefault {
                        ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    },
                    58..62,
                    None,
                )]
            },
        )
    }

    #[test]
    fn default_value_distinct_bool_slice() {
        check(
            r#"
                defaults :: () {
                    x : distinct []bool;
                }
            "#,
            expect![[r#"
                main::defaults : () -> void
                3 : void
                4 : () -> void
                l0 : distinct'0 []bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::DeclTypeHasNoDefault {
                        ty: Ty::Distinct {
                            fqn: None,
                            uid: 0,
                            sub_ty: Ty::Slice {
                                sub_ty: Ty::Bool.into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    58..73,
                    None,
                )]
            },
        )
    }

    #[test]
    fn default_value_distinct_struct_with_str() {
        check(
            r#"
                defaults :: () {
                    x : distinct struct {
                        foo: str,
                        bar: u8,
                    };
                }
            "#,
            expect![[r#"
                main::defaults : () -> void
                4 : void
                5 : () -> void
                l0 : distinct'1 struct'0 {foo: str, bar: u8}
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::DeclTypeHasNoDefault {
                        ty: Ty::Distinct {
                            fqn: None,
                            uid: 1,
                            sub_ty: Ty::Struct {
                                anonymous: false,
                                fqn: None,
                                uid: 0,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("foo")),
                                        ty: Ty::String.into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("bar")),
                                        ty: Ty::UInt(8).into(),
                                    },
                                ],
                            }
                            .into(),
                        }
                        .into(),
                    },
                    58..164,
                    None,
                )]
            },
        )
    }

    #[test]
    fn default_value_with_uninferred_globals() {
        // this is to check for a bug where errors would get reported twice
        // because when an uninferred global was reached it would
        // throw away all the previously done statement inferring.
        check(
            r#"
                Foo :: distinct u8;
                Bar :: ^Foo;
                Baz :: struct { a: Bar };

                defaults :: () {
                    x: ^i32;
                    Baz;
                }
            "#,
            expect![[r#"
                main::Bar : type
                main::Baz : type
                main::Foo : type
                main::defaults : () -> void
                1 : type
                2 : type
                3 : type
                5 : type
                8 : type
                9 : void
                10 : () -> void
                l0 : ^i32
            "#]],
            |_| {
                // under the bug, this appears twice
                [(
                    TyDiagnosticKind::DeclTypeHasNoDefault {
                        ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                    },
                    165..169,
                    None,
                )]
            },
        )
    }

    #[test]
    fn anon_struct() {
        check(
            r#"
                anon :: () {
                    foo := .{
                        a = 5,
                        b = "hello",
                        c = 5.5,
                    };
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : {uint}
                1 : str
                2 : {float}
                3 : struct ~{a: {uint}, b: str, c: {float}}
                4 : void
                5 : () -> void
                l0 : struct ~{a: {uint}, b: str, c: {float}}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_struct_into_known_struct() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo : Foo_Type = .{
                        a = 5,
                        b = "hello",
                        c = 5.5,
                    };
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                5 : u8
                6 : str
                7 : f64
                8 : main::Foo_Type
                9 : void
                10 : () -> void
                l0 : main::Foo_Type
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_struct_into_known_struct_mixed_fields() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo : Foo_Type = .{
                        b = "hello",
                        c = 5.5,
                        a = 5,
                    };
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                5 : str
                6 : f64
                7 : u8
                8 : main::Foo_Type
                9 : void
                10 : () -> void
                l0 : main::Foo_Type
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_struct_into_known_struct_by_inference() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo := .{
                        b = "hello",
                        c = 5.5,
                        a = 5,
                    };

                    bar : Foo_Type = foo;
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                4 : str
                5 : f64
                6 : u8
                7 : main::Foo_Type
                9 : main::Foo_Type
                10 : void
                11 : () -> void
                l0 : main::Foo_Type
                l1 : main::Foo_Type
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_struct_as_known_struct() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo := .{
                        b = "hello",
                        c = 5.5,
                        a = 5,
                    };

                    bar := Foo_Type.(foo);
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                4 : str
                5 : f64
                6 : u8
                7 : main::Foo_Type
                8 : main::Foo_Type
                10 : main::Foo_Type
                11 : void
                12 : () -> void
                l0 : main::Foo_Type
                l1 : main::Foo_Type
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_struct_as_known_struct_diff_field_ty() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    c : f32 = 5.5;

                    foo := Foo_Type.(.{
                        b = "hello",
                        c = c,
                        a = 3.14,
                    });
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                5 : f32
                6 : str
                7 : f32
                8 : {float}
                9 : struct ~{b: str, c: f32, a: {float}}
                11 : main::Foo_Type
                12 : void
                13 : () -> void
                l0 : f32
                l1 : main::Foo_Type
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_struct_into_known_struct_missing_field() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo : Foo_Type = .{
                        a = 5,
                        b = "hello",
                    };
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                5 : {uint}
                6 : str
                7 : struct ~{a: {uint}, b: str}
                8 : void
                9 : () -> void
                l0 : main::Foo_Type
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Struct {
                                anonymous: false,
                                fqn: Some(hir::Fqn {
                                    file: hir::FileName(i.intern("main.capy")),
                                    name: hir::Name(i.intern("Foo_Type")),
                                }),
                                uid: 0,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("a")),
                                        ty: Ty::UInt(8).into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("b")),
                                        ty: Ty::String.into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("c")),
                                        ty: Ty::Float(64).into(),
                                    },
                                ],
                            }
                            .into(),
                        ),
                        found: Ty::Struct {
                            anonymous: true,
                            fqn: None,
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::UInt(0).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::String.into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    207..299,
                    None,
                )]
            },
        )
    }

    #[test]
    fn anon_struct_into_known_struct_extra_field() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo : Foo_Type = .{
                        a = 5,
                        b = "hello",
                        c = 3.14,
                        d = true,
                    };
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                5 : {uint}
                6 : str
                7 : {float}
                8 : bool
                9 : struct ~{a: {uint}, b: str, c: {float}, d: bool}
                10 : void
                11 : () -> void
                l0 : main::Foo_Type
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Struct {
                                anonymous: false,
                                fqn: Some(hir::Fqn {
                                    file: hir::FileName(i.intern("main.capy")),
                                    name: hir::Name(i.intern("Foo_Type")),
                                }),
                                uid: 0,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("a")),
                                        ty: Ty::UInt(8).into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("b")),
                                        ty: Ty::String.into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("c")),
                                        ty: Ty::Float(64).into(),
                                    },
                                ],
                            }
                            .into(),
                        ),
                        found: Ty::Struct {
                            anonymous: true,
                            fqn: None,
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::UInt(0).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("c")),
                                    ty: Ty::Float(0).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("d")),
                                    ty: Ty::Bool.into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    207..367,
                    None,
                )]
            },
        )
    }

    #[test]
    fn anon_struct_into_known_struct_misnamed_field() {
        check(
            r#"
                Foo_Type :: struct {
                    a: u8,
                    b: str,
                    c: f64,
                };

                anon :: () {
                    foo : Foo_Type = .{
                        a = 5,
                        b = "hello",
                        last = 0.3,
                    };
                }
            "#,
            expect![[r#"
                main::Foo_Type : type
                main::anon : () -> void
                3 : type
                5 : {uint}
                6 : str
                7 : {float}
                8 : struct ~{a: {uint}, b: str, last: {float}}
                9 : void
                10 : () -> void
                l0 : main::Foo_Type
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Struct {
                                anonymous: false,
                                fqn: Some(hir::Fqn {
                                    file: hir::FileName(i.intern("main.capy")),
                                    name: hir::Name(i.intern("Foo_Type")),
                                }),
                                uid: 0,
                                members: vec![
                                    MemberTy {
                                        name: hir::Name(i.intern("a")),
                                        ty: Ty::UInt(8).into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("b")),
                                        ty: Ty::String.into(),
                                    },
                                    MemberTy {
                                        name: hir::Name(i.intern("c")),
                                        ty: Ty::Float(64).into(),
                                    },
                                ],
                            }
                            .into(),
                        ),
                        found: Ty::Struct {
                            anonymous: true,
                            fqn: None,
                            uid: 0,
                            members: vec![
                                MemberTy {
                                    name: hir::Name(i.intern("a")),
                                    ty: Ty::UInt(0).into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("b")),
                                    ty: Ty::String.into(),
                                },
                                MemberTy {
                                    name: hir::Name(i.intern("last")),
                                    ty: Ty::Float(0).into(),
                                },
                            ],
                        }
                        .into(),
                    },
                    207..335,
                    None,
                )]
            },
        )
    }

    #[test]
    fn anon_array() {
        check(
            r#"
                anon :: () {
                    foo := .[1, 2, 3];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : [3]~{uint}
                4 : void
                5 : () -> void
                l0 : [3]~{uint}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_into_known_array() {
        check(
            r#"
                anon :: () {
                    foo : [3]u16 = .[1, 2, 3];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : usize
                3 : u16
                4 : u16
                5 : u16
                6 : [3]u16
                7 : void
                8 : () -> void
                l0 : [3]u16
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_into_known_slice() {
        check(
            r#"
                anon :: () {
                    foo : []u16 = .[1, 2, 3];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                2 : u16
                3 : u16
                4 : u16
                5 : [3]u16
                6 : void
                7 : () -> void
                l0 : []u16
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_as_known_array() {
        check(
            r#"
                anon :: () {
                    foo := [3]u128.(.[1, 2, 3]);
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : u128
                1 : u128
                2 : u128
                3 : [3]u128
                4 : usize
                7 : [3]u128
                8 : void
                9 : () -> void
                l0 : [3]u128
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_as_known_slice() {
        check(
            r#"
                anon :: () {
                    foo := []i8.(.[1, 2, 3]);
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : i8
                1 : i8
                2 : i8
                3 : [3]i8
                6 : []i8
                7 : void
                8 : () -> void
                l0 : []i8
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_into_known_array_too_large() {
        check(
            r#"
                anon :: () {
                    foo : [3]i16 = .[1, 2, 3, 4];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : usize
                3 : {uint}
                4 : {uint}
                5 : {uint}
                6 : {uint}
                7 : [4]~{uint}
                8 : void
                9 : () -> void
                l0 : [3]i16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Array {
                                anonymous: false,
                                size: 3,
                                sub_ty: Ty::IInt(16).into(),
                            }
                            .into(),
                        ),
                        found: Ty::Array {
                            anonymous: true,
                            size: 4,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    },
                    65..78,
                    None,
                )]
            },
        )
    }

    #[test]
    fn anon_array_into_known_array_too_small() {
        check(
            r#"
                anon :: () {
                    foo : [3]i16 = .[1, 2];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : usize
                3 : {uint}
                4 : {uint}
                5 : [2]~{uint}
                6 : void
                7 : () -> void
                l0 : [3]i16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(
                            Ty::Array {
                                anonymous: false,
                                size: 3,
                                sub_ty: Ty::IInt(16).into(),
                            }
                            .into(),
                        ),
                        found: Ty::Array {
                            anonymous: true,
                            size: 2,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    },
                    65..72,
                    None,
                )]
            },
        )
    }

    #[test]
    fn anon_array_into_known_array_by_inference() {
        check(
            r#"
                anon :: () {
                    foo := .[1, 2];

                    bar : [2]i128 = foo;
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : i128
                1 : i128
                2 : [2]i128
                3 : usize
                6 : [2]i128
                7 : void
                8 : () -> void
                l0 : [2]i128
                l1 : [2]i128
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_into_known_slice_by_inference() {
        check(
            r#"
                anon :: () {
                    foo := .[1, 2];

                    bar : []u128 = foo;
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : u128
                1 : u128
                2 : [2]u128
                5 : [2]u128
                6 : void
                7 : () -> void
                l0 : [2]u128
                l1 : []u128
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_signed_int_inner_type() {
        check(
            r#"
                anon :: () {
                    foo := .[4, -5, 6];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : {int}
                1 : {int}
                2 : {int}
                3 : {int}
                4 : [3]~{int}
                5 : void
                6 : () -> void
                l0 : [3]~{int}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_i64_inner_type() {
        check(
            r#"
                anon :: () {
                    second : i64 = 42;

                    foo := .[4, second, 6];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                1 : i64
                2 : i64
                3 : i64
                4 : i64
                5 : [3]~i64
                6 : void
                7 : () -> void
                l0 : i64
                l1 : [3]~i64
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_i64_i128_inner_type() {
        check(
            r#"
                anon :: () {
                    second : i64 = 42;
                    third : i128 = 5;

                    foo := .[4, second, third, 7];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                1 : i64
                3 : i128
                4 : i128
                5 : i64
                6 : i128
                7 : i128
                8 : [4]~i128
                9 : void
                10 : () -> void
                l0 : i64
                l1 : i128
                l2 : [4]~i128
            "#]],
            |_| [],
        )
    }

    #[test]
    fn anon_array_mismatch_inner_types() {
        // this SHOULD return an error.
        // I think automatically casting this to any would be unexpected
        check(
            r#"
                anon :: () {
                    foo := .[1, -2, true, "Hello, Sailor!", 0.1];
                }
            "#,
            expect![[r#"
                main::anon : () -> void
                0 : {uint}
                1 : {int}
                2 : {int}
                3 : bool
                4 : str
                5 : {float}
                6 : [5]~<unknown>
                7 : void
                8 : () -> void
                l0 : [5]~<unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::IInt(0).into()),
                        found: Ty::Bool.into(),
                    },
                    66..70,
                    None,
                )]
            },
        )
    }

    #[test]
    fn get_const_on_cyclic_globals() {
        // check for https://github.com/capy-language/capy/issues/32

        // todo: if a is inferred before b, then you will get two GlobalNotConst errors
        // but if b is inferred before a, then you will get one GlobalNotConst errors
        //
        // I personally like the second result more, but the errors should be consistent no matter
        // which way it happens.
        //
        // Also there was a weird thing where while testing the example code here I would get a
        // before b, but then while doing `cargo run -- run examples/test.capy` with the example
        // code i would get b before a. I was only able to fix this by changing FxHashMap/Set in
        // the `topo` crate to an IndexMap/Set
        check(
            r#"
                foo :: 1;
                ptr :: 2;
                idx :: 5;
                b   :: a;
                old_gandalf :: struct {};
                b.a = b.a + 1;
            "#,
            expect![[r#"
                main::a : i32
                main::b : <unknown>
                main::foo : i32
                main::idx : i32
                main::old_gandalf : type
                main::ptr : i32
                0 : i32
                1 : i32
                2 : i32
                3 : <unknown>
                4 : type
                5 : <unknown>
                6 : <unknown>
                7 : i32
                8 : i32
            "#]],
            |i| {
                [
                    (
                        TyDiagnosticKind::NotYetResolved {
                            fqn: hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("a")),
                            },
                        },
                        102..103,
                        None,
                    ),
                    (TyDiagnosticKind::GlobalNotConst, 169..176, None),
                ]
            },
        )
    }

    #[test]
    fn recursive_global() {
        // check for https://github.com/capy-language/capy/issues/30
        check(
            r#"
                a :: a;
            "#,
            expect![[r#"
                main::a : <unknown>
                0 : <unknown>
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("a")),
                        },
                    },
                    22..23,
                    None,
                )]
            },
        )
    }

    #[test]
    fn empty_enum() {
        check(
            r#"
                My_Awesome_Enum :: enum {
                    Foo,
                    Bar
                };

                main :: () {
                    my_foo : My_Awesome_Enum.Foo = My_Awesome_Enum.Foo.(());
                    my_bar : My_Awesome_Enum.Bar = My_Awesome_Enum.Bar.(());
                }
            "#,
            expect![[r#"
                main::My_Awesome_Enum : type
                main::main : () -> void
                0 : type
                1 : type
                3 : void
                4 : type
                6 : main::My_Awesome_Enum.Foo
                7 : type
                9 : void
                10 : type
                12 : main::My_Awesome_Enum.Bar
                13 : void
                14 : () -> void
                l0 : main::My_Awesome_Enum.Foo
                l1 : main::My_Awesome_Enum.Bar
            "#]],
            |_| [],
        )
    }

    #[test]
    fn typed_enum_with_discriminants() {
        check(
            r#"
                My_Awesome_Enum :: enum {
                    Foo,
                    Bar: i32,
                    Baz: str | 42,
                    Qux: bool
                };

                main :: () {
                    my_foo : My_Awesome_Enum.Foo = My_Awesome_Enum.Foo.(());
                    my_bar : My_Awesome_Enum.Bar = My_Awesome_Enum.Bar.(5);
                    my_baz : My_Awesome_Enum.Baz = My_Awesome_Enum.Baz.("hello");
                    my_qux : My_Awesome_Enum.Qux = My_Awesome_Enum.Qux.(true);
                }
            "#,
            expect![[r#"
                main::My_Awesome_Enum : type
                main::main : () -> void
                2 : u8
                4 : type
                5 : type
                7 : void
                8 : type
                10 : main::My_Awesome_Enum.Foo
                11 : type
                13 : {uint}
                14 : type
                16 : main::My_Awesome_Enum.Bar
                17 : type
                19 : str
                20 : type
                22 : main::My_Awesome_Enum.Baz
                23 : type
                25 : bool
                26 : type
                28 : main::My_Awesome_Enum.Qux
                29 : void
                30 : () -> void
                l0 : main::My_Awesome_Enum.Foo
                l1 : main::My_Awesome_Enum.Bar
                l2 : main::My_Awesome_Enum.Baz
                l3 : main::My_Awesome_Enum.Qux
            "#]],
            |_| [],
        )
    }

    #[test]
    fn weak_to_strong_u8_array_of_arrays() {
        // check for https://github.com/capy-language/capy/issues/30
        check(
            r#"
                main :: () {
                    x : u8 = 1;
                    y : u8 = 2;
                    z : u8 = 3;

                    arr : [3][3][3]u8 = .[
                        .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                        .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                        .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                    ];
                }
            "#,
            expect![[r#"
                main::main : () -> void
                1 : u8
                3 : u8
                5 : u8
                6 : usize
                7 : usize
                8 : usize
                13 : u8
                14 : u8
                15 : u8
                16 : [3]u8
                17 : u8
                18 : u8
                19 : u8
                20 : [3]u8
                21 : u8
                22 : u8
                23 : u8
                24 : [3]u8
                25 : [3][3]u8
                26 : u8
                27 : u8
                28 : u8
                29 : [3]u8
                30 : u8
                31 : u8
                32 : u8
                33 : [3]u8
                34 : u8
                35 : u8
                36 : u8
                37 : [3]u8
                38 : [3][3]u8
                39 : u8
                40 : u8
                41 : u8
                42 : [3]u8
                43 : u8
                44 : u8
                45 : u8
                46 : [3]u8
                47 : u8
                48 : u8
                49 : u8
                50 : [3]u8
                51 : [3][3]u8
                52 : [3][3][3]u8
                53 : void
                54 : () -> void
                l0 : u8
                l1 : u8
                l2 : u8
                l3 : [3][3][3]u8
            "#]],
            |_| [],
        )
    }

    #[test]
    fn weak_to_strong_uint_array_of_arrays() {
        // check for https://github.com/capy-language/capy/issues/30
        check(
            r#"
                main :: () {
                    x := 1;
                    y := 2;
                    z := 3;

                    arr : [3][3][3]u8 = .[
                        .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                        .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                        .[ .[x, y, z], .[x, y, z], .[x, y, z] ],
                    ];
                }
            "#,
            expect![[r#"
                main::main : () -> void
                0 : u8
                1 : u8
                2 : u8
                3 : usize
                4 : usize
                5 : usize
                10 : u8
                11 : u8
                12 : u8
                13 : [3]u8
                14 : u8
                15 : u8
                16 : u8
                17 : [3]u8
                18 : u8
                19 : u8
                20 : u8
                21 : [3]u8
                22 : [3][3]u8
                23 : u8
                24 : u8
                25 : u8
                26 : [3]u8
                27 : u8
                28 : u8
                29 : u8
                30 : [3]u8
                31 : u8
                32 : u8
                33 : u8
                34 : [3]u8
                35 : [3][3]u8
                36 : u8
                37 : u8
                38 : u8
                39 : [3]u8
                40 : u8
                41 : u8
                42 : u8
                43 : [3]u8
                44 : u8
                45 : u8
                46 : u8
                47 : [3]u8
                48 : [3][3]u8
                49 : [3][3][3]u8
                50 : void
                51 : () -> void
                l0 : u8
                l1 : u8
                l2 : u8
                l3 : [3][3][3]u8
            "#]],
            |_| [],
        )
    }

    #[test]
    fn autocast_variant_to_enum_variable() {
        check(
            r#"
                Animal :: enum {
                    Dog: str,
                    Fish: i32, // maybe this is the fish's age or something
                };

                main :: () {
                    my_dog := Animal.Dog.("George");
                    my_fish := Animal.Fish.(1000);

                    animal_1 : Animal = my_dog;
                    animal_2 : Animal = my_fish;
                }
            "#,
            expect![[r#"
                main::Animal : type
                main::main : () -> void
                2 : type
                3 : str
                4 : type
                6 : main::Animal.Dog
                7 : {uint}
                8 : type
                10 : main::Animal.Fish
                12 : main::Animal.Dog
                14 : main::Animal.Fish
                15 : void
                16 : () -> void
                l0 : main::Animal.Dog
                l1 : main::Animal.Fish
                l2 : main::Animal
                l3 : main::Animal
            "#]],
            |_| [],
        )
    }

    #[test]
    fn autocast_variant_to_enum_function() {
        check(
            r#"
                Animal :: enum {
                    Dog: str,
                    Fish: i32, // maybe this is the fish's age or something
                };

                main :: () {
                    my_dog := Animal.Dog.("George");
                    my_fish := Animal.Fish.(1000);

                    go_do_animal_stuff_idk(my_dog);
                    go_do_animal_stuff_idk(my_fish);
                }

                go_do_animal_stuff_idk :: (animal: Animal) {
                    // imagine the craziest code here
                }
            "#,
            expect![[r#"
                main::Animal : type
                main::go_do_animal_stuff_idk : (main::Animal) -> void
                main::main : () -> void
                2 : type
                3 : str
                4 : type
                6 : main::Animal.Dog
                7 : {uint}
                8 : type
                10 : main::Animal.Fish
                11 : (main::Animal) -> void
                12 : main::Animal.Dog
                13 : void
                14 : (main::Animal) -> void
                15 : main::Animal.Fish
                16 : void
                17 : void
                18 : () -> void
                20 : void
                21 : (main::Animal) -> void
                l0 : main::Animal.Dog
                l1 : main::Animal.Fish
            "#]],
            |_| [],
        )
    }

    #[test]
    fn cast_variant_to_enum_function() {
        check(
            r#"
                Animal :: enum {
                    Dog: str,
                    Fish: i32, // maybe this is the fish's age or something
                };

                main :: () {
                    my_dog := Animal.Dog.("George");
                    my_fish := Animal.Fish.(1000);

                    go_do_animal_stuff_idk(Animal.(my_dog));
                    go_do_animal_stuff_idk(Animal.(my_fish));
                }

                go_do_animal_stuff_idk :: (animal: Animal) {
                    // imagine the craziest code here
                }
            "#,
            expect![[r#"
                main::Animal : type
                main::go_do_animal_stuff_idk : (main::Animal) -> void
                main::main : () -> void
                2 : type
                3 : str
                4 : type
                6 : main::Animal.Dog
                7 : {uint}
                8 : type
                10 : main::Animal.Fish
                11 : (main::Animal) -> void
                12 : main::Animal.Dog
                14 : main::Animal
                15 : void
                16 : (main::Animal) -> void
                17 : main::Animal.Fish
                19 : main::Animal
                20 : void
                21 : void
                22 : () -> void
                24 : void
                25 : (main::Animal) -> void
                l0 : main::Animal.Dog
                l1 : main::Animal.Fish
            "#]],
            |_| [],
        )
    }

    #[test]
    fn switch() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    switch e in clicked {
                        Page_Load => {
                            e;
                            1; // this is done so that the `e`s are clearly visible below
                        },
                        Page_Unload => {
                            e;
                            true;
                        },
                        Key_Press => {
                            e;
                            "";
                        },
                        Paste => {
                            e;
                            ' ';
                        }
                        Click => {
                            e;
                            e.x;
                        }
                    }
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : main::Web_Event
                13 : main::Web_Event.Page_Load
                14 : {uint}
                15 : void
                16 : main::Web_Event.Page_Unload
                17 : bool
                18 : void
                19 : main::Web_Event.Key_Press
                20 : str
                21 : void
                22 : main::Web_Event.Paste
                23 : char
                24 : void
                25 : main::Web_Event.Click
                26 : main::Web_Event.Click
                27 : i64
                28 : void
                29 : void
                30 : void
                31 : () -> void
                l0 : main::Web_Event
            "#]],
            |_| [],
        )
    }

    #[test]
    fn switch_val() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    val : i16 = switch e in clicked {
                        Page_Load => {
                            e;
                            10
                        },
                        Page_Unload => {
                            e;
                            20
                        },
                        Key_Press => {
                            e;
                            30
                        },
                        Paste => {
                            e;
                            40
                        }
                        Click => {
                            e;
                            50
                        }
                    };
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                13 : main::Web_Event
                14 : main::Web_Event.Page_Load
                15 : i16
                16 : i16
                17 : main::Web_Event.Page_Unload
                18 : i16
                19 : i16
                20 : main::Web_Event.Key_Press
                21 : i16
                22 : i16
                23 : main::Web_Event.Paste
                24 : i16
                25 : i16
                26 : main::Web_Event.Click
                27 : i16
                28 : i16
                29 : i16
                30 : void
                31 : () -> void
                l0 : main::Web_Event
                l1 : i16
            "#]],
            |_| [],
        )
    }

    #[test]
    fn switch_mismatch_val() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    val : u8 = switch e in clicked {
                        Page_Load => {
                            e;
                            10
                        },
                        Page_Unload => {
                            e;
                            20
                        },
                        Key_Press => {
                            e;
                            "hello"
                        },
                        Paste => {
                            e;
                            true
                        }
                        Click => {
                            e;
                            ' '
                        }
                    };
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                13 : main::Web_Event
                14 : main::Web_Event.Page_Load
                15 : {uint}
                16 : {uint}
                17 : main::Web_Event.Page_Unload
                18 : {uint}
                19 : {uint}
                20 : main::Web_Event.Key_Press
                21 : str
                22 : str
                23 : main::Web_Event.Paste
                24 : bool
                25 : bool
                26 : main::Web_Event.Click
                27 : char
                28 : char
                29 : <unknown>
                30 : void
                31 : () -> void
                l0 : main::Web_Event
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::SwitchMismatch {
                        second: Ty::String.into(),
                        first: Ty::UInt(0).into(),
                    },
                    836..930,
                    None,
                )]
            },
        )
    }

    #[test]
    fn switch_missing_variant() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    val : i128 = switch e in clicked {
                        Page_Load => {
                            e;
                            10
                        },
                        Page_Unload => {
                            e;
                            20
                        },
                        Key_Press => {
                            e;
                            "hello"
                        },
                    };
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                13 : main::Web_Event
                14 : main::Web_Event.Page_Load
                15 : {uint}
                16 : {uint}
                17 : main::Web_Event.Page_Unload
                18 : {uint}
                19 : {uint}
                20 : main::Web_Event.Key_Press
                21 : str
                22 : str
                23 : <unknown>
                24 : void
                25 : () -> void
                l0 : main::Web_Event
                l1 : i128
            "#]],
            |i| {
                [
                    (
                        TyDiagnosticKind::SwitchMismatch {
                            second: Ty::String.into(),
                            first: Ty::UInt(0).into(),
                        },
                        838..932,
                        None,
                    ),
                    (
                        TyDiagnosticKind::SwitchDoesNotCoverVariant {
                            ty: Ty::Variant {
                                enum_fqn: Some(hir::Fqn {
                                    file: hir::FileName(i.intern("main.capy")),
                                    name: hir::Name(i.intern("Web_Event")),
                                }),
                                enum_uid: 6,
                                variant_name: hir::Name(i.intern("Paste")),
                                uid: 3,
                                sub_ty: Ty::String.into(),
                                discriminant: 3,
                            }
                            .into(),
                        },
                        521..955,
                        None,
                    ),
                    (
                        TyDiagnosticKind::SwitchDoesNotCoverVariant {
                            ty: Ty::Variant {
                                enum_fqn: Some(hir::Fqn {
                                    file: hir::FileName(i.intern("main.capy")),
                                    name: hir::Name(i.intern("Web_Event")),
                                }),
                                enum_uid: 6,
                                variant_name: hir::Name(i.intern("Click")),
                                uid: 5,
                                sub_ty: Ty::Struct {
                                    anonymous: false,
                                    fqn: None,
                                    uid: 4,
                                    members: vec![
                                        MemberTy {
                                            name: hir::Name(i.intern("x")),
                                            ty: Ty::IInt(64).into(),
                                        },
                                        MemberTy {
                                            name: hir::Name(i.intern("y")),
                                            ty: Ty::IInt(64).into(),
                                        },
                                    ],
                                }
                                .into(),
                                discriminant: 4,
                            }
                            .into(),
                        },
                        521..955,
                        None,
                    ),
                ]
            },
        )
    }

    #[test]
    fn switch_default() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    val : u16 = switch e in clicked {
                        Page_Load => {
                            e;
                            10
                        },
                        Page_Unload => {
                            e;
                            20
                        },
                        Key_Press => {
                            e;
                            30
                        },
                        _ => 40,
                    };
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                13 : main::Web_Event
                14 : main::Web_Event.Page_Load
                15 : u16
                16 : u16
                17 : main::Web_Event.Page_Unload
                18 : u16
                19 : u16
                20 : main::Web_Event.Key_Press
                21 : u16
                22 : u16
                23 : u16
                24 : u16
                25 : void
                26 : () -> void
                l0 : main::Web_Event
                l1 : u16
            "#]],
            |_| [],
        )
    }

    #[test]
    fn switch_default_mismatch() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    val : u16 = switch e in clicked {
                        Page_Load => {
                            e;
                            10
                        },
                        Page_Unload => {
                            e;
                            20
                        },
                        Key_Press => {
                            e;
                            30
                        },
                        _ => "hello",
                    };
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                13 : main::Web_Event
                14 : main::Web_Event.Page_Load
                15 : {uint}
                16 : {uint}
                17 : main::Web_Event.Page_Unload
                18 : {uint}
                19 : {uint}
                20 : main::Web_Event.Key_Press
                21 : {uint}
                22 : {uint}
                23 : str
                24 : <unknown>
                25 : void
                26 : () -> void
                l0 : main::Web_Event
                l1 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::SwitchMismatch {
                        second: Ty::String.into(),
                        first: Ty::UInt(0).into(),
                    },
                    957..964,
                    None,
                )]
            },
        )
    }

    #[test]
    fn enum_single_unused_discriminant() {
        check(
            r#"
                foo :: () {
                    Web_Event :: enum {
                        Page_Load,
                        Page_Unload,
                        Key_Press: char,
                        Paste: str | 10,
                        Click: struct {
                            x: i64,
                            y: i64,
                        },
                        Unclick: struct {
                            x: i64,
                            y: i64,
                        }
                    };

                    clicked : Web_Event = Web_Event.Click.{x=10, y=20};
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : u8
                9 : type
                11 : type
                13 : i64
                14 : i64
                15 : .Click'5
                16 : void
                17 : () -> void
                l0 : type
                l1 : enum '8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 2, Paste: str | 10, Click: struct'4 {x: i64, y: i64} | 11, Unclick: struct'6 {x: i64, y: i64} | 12}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn enum_double_unused_discriminant() {
        check(
            r#"
                foo :: () {
                    Web_Event :: enum {
                        Page_Load,
                        Page_Unload,
                        Key_Press: char,
                        Paste: str | 10,
                        Click: struct {
                            x: i64,
                            y: i64,
                        } | 10,
                        Unclick: struct {
                            x: i64,
                            y: i64,
                        }
                    };

                    clicked : Web_Event = Web_Event.Click.{x=10, y=20};
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : u8
                6 : u8
                10 : type
                12 : type
                14 : i64
                15 : i64
                16 : .Click'5
                17 : void
                18 : () -> void
                l0 : type
                l1 : enum '8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 2, Paste: str | 10, Click: struct'4 {x: i64, y: i64} | 11, Unclick: struct'6 {x: i64, y: i64} | 12}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::DiscriminantUsedAlready { value: 10 },
                    363..365,
                    None,
                )]
            },
        )
    }

    #[test]
    fn enum_single_used_discriminant() {
        check(
            r#"
                foo :: () {
                    Web_Event :: enum {
                        Page_Load,
                        Page_Unload,
                        Key_Press: char,
                        Paste: str,
                        Click: struct {
                            x: i64,
                            y: i64,
                        } | 2,
                        Unclick: struct {
                            x: i64,
                            y: i64,
                        }
                    };

                    clicked : Web_Event = Web_Event.Click.{x=10, y=20};
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                5 : u8
                9 : type
                11 : type
                13 : i64
                14 : i64
                15 : .Click'5
                16 : void
                17 : () -> void
                l0 : type
                l1 : enum '8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 3, Paste: str | 4, Click: struct'4 {x: i64, y: i64} | 2, Unclick: struct'6 {x: i64, y: i64} | 5}
            "#]],
            |_| [],
        )
    }

    #[test]
    fn enum_double_used_discriminant() {
        check(
            r#"
                foo :: () {
                    Web_Event :: enum {
                        Page_Load,
                        Page_Unload,
                        Key_Press: char,
                        Paste: str | 2,
                        Click: struct {
                            x: i64,
                            y: i64,
                        } | 2,
                        Unclick: struct {
                            x: i64,
                            y: i64,
                        }
                    };

                    clicked : Web_Event = Web_Event.Click.{x=10, y=20};
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : u8
                6 : u8
                10 : type
                12 : type
                14 : i64
                15 : i64
                16 : .Click'5
                17 : void
                18 : () -> void
                l0 : type
                l1 : enum '8 {Page_Load | 0, Page_Unload | 1, Key_Press: char | 3, Paste: str | 2, Click: struct'4 {x: i64, y: i64} | 4, Unclick: struct'6 {x: i64, y: i64} | 5}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::DiscriminantUsedAlready { value: 2 },
                    362..363,
                    None,
                )]
            },
        )
    }

    #[test]
    fn only_report_one_if_mismatch() {
        check(
            r#"
                foo :: () {
                    if true {
                        42
                    } else if true {
                        42
                    } else if true {
                        "hello"
                    } else if true {
                        "hello"
                    } else if true {
                        "hello"
                    } else if true {
                        42
                    } else {
                        42
                    };
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : bool
                1 : {uint}
                2 : {uint}
                3 : bool
                4 : {uint}
                5 : {uint}
                6 : bool
                7 : str
                8 : str
                9 : bool
                10 : str
                11 : str
                12 : bool
                13 : str
                14 : str
                15 : bool
                16 : {uint}
                17 : {uint}
                18 : {uint}
                19 : {uint}
                20 : {uint}
                21 : <unknown>
                22 : <unknown>
                23 : <unknown>
                24 : <unknown>
                25 : <unknown>
                26 : void
                27 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IfMismatch {
                        first: Ty::String.into(),
                        second: Ty::UInt(0).into(),
                    },
                    315..498,
                    None,
                )]
            },
        )
    }

    #[test]
    fn compare_bool_to_bool() {
        check(
            r#"
                foo :: () {
                    true == false;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : bool
                1 : bool
                2 : bool
                3 : void
                4 : () -> void
            "#]],
            |_| [],
        )
    }

    #[test]
    fn reinfer_final_usages() {
        // check for https://github.com/capy-language/capy/issues/41
        //
        // this was essentially caused by the fact that `i` actually doesn't have a type until the
        // very very end, where in `finish_body` it gets weak type replaced by u64--but what was
        // going wrong was that before the type was getting weak type replaced, all the local
        // usages were being cleared, making it impossible for them to ALSO get weak type replaced.
        // this is fixed now.
        check(
            r#"
                log2_u64 :: (n: u64) -> u64 {
                    n := n;
                    i := 0;
                    while n != 0 {
                        n = n << 1;
                        i = i + 1;
                    }
                    i
                }
            "#,
            expect![[r#"
                main::log2_u64 : (u64) -> u64
                2 : u64
                3 : u64
                4 : u64
                5 : u64
                6 : bool
                7 : u64
                8 : u64
                9 : u64
                10 : u64
                11 : u64
                12 : u64
                13 : u64
                14 : u64
                15 : void
                16 : void
                17 : u64
                18 : u64
                19 : (u64) -> u64
                l0 : u64
                l1 : u64
            "#]],
            |_| [],
        )
    }

    #[test]
    fn unwrap_directive() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #unwrap(clicked, Web_Event.Click);
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : main::Web_Event
                13 : type
                14 : type
                15 : main::Web_Event.Click
                16 : void
                17 : () -> void
                l0 : main::Web_Event
                l1 : main::Web_Event.Click
            "#]],
            |_| [],
        )
    }

    #[test]
    fn unwrap_directive_no_arg() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #unwrap();
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : <unknown>
                13 : void
                14 : () -> void
                l0 : main::Web_Event
                l1 : <unknown>
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::MissingArg {
                            expected: ExpectedTy::Enum,
                        },
                        529..529,
                        None,
                    ),
                    (
                        TyDiagnosticKind::MissingArg {
                            expected: ExpectedTy::Concrete(Ty::Type.into()),
                        },
                        529..529,
                        None,
                    ),
                ]
            },
        )
    }

    #[test]
    fn unwrap_directive_one_arg_incorrect() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #unwrap(5);
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : {uint}
                13 : <unknown>
                14 : void
                15 : () -> void
                l0 : main::Web_Event
                l1 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Enum,
                        found: Ty::UInt(0).into(),
                    },
                    529..530,
                    None,
                )]
            },
        )
    }

    #[test]
    fn unwrap_directive_two_args_incorrect() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #unwrap(clicked, 5);
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : main::Web_Event
                13 : {uint}
                14 : <unknown>
                15 : void
                16 : () -> void
                l0 : main::Web_Event
                l1 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Concrete(Ty::Type.into()),
                        found: Ty::UInt(0).into(),
                    },
                    538..539,
                    None,
                )]
            },
        )
    }

    #[test]
    fn unwrap_directive_two_args_non_variant() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #unwrap(clicked, i32);
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : main::Web_Event
                13 : type
                14 : <unknown>
                15 : void
                16 : () -> void
                l0 : main::Web_Event
                l1 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ExpectedTy::Variant,
                        found: Ty::IInt(32).into(),
                    },
                    538..541,
                    None,
                )]
            },
        )
    }

    #[test]
    fn unwrap_directive_extra_arg() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #unwrap(clicked, Web_Event.Click, 42, bool);
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : main::Web_Event
                13 : type
                14 : type
                15 : {uint}
                16 : type
                17 : <unknown>
                18 : void
                19 : () -> void
                l0 : main::Web_Event
                l1 : <unknown>
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::ExtraArg {
                            found: Ty::UInt(0).into(),
                        },
                        538..553,
                        None,
                    ),
                    (
                        TyDiagnosticKind::ExtraArg {
                            found: Ty::Type.into(),
                        },
                        538..553,
                        None,
                    ),
                ]
            },
        )
    }

    #[test]
    fn unknown_compiler_directive() {
        check(
            r#"
                Web_Event :: enum {
                    Page_Load,
                    Page_Unload,
                    Key_Press: char,
                    Paste: str,
                    Click: struct {
                        x: i64,
                        y: i64,
                    },
                };

                foo :: () {
                    clicked : Web_Event = Web_Event.Click.{
                        x = 20,
                        y = 80
                    };

                    unwrapped := #foo(clicked, Web_Event.Click, 42, bool);
                }
            "#,
            expect![[r#"
                main::Web_Event : type
                main::foo : () -> void
                5 : type
                7 : type
                9 : i64
                10 : i64
                11 : main::Web_Event.Click
                12 : main::Web_Event
                13 : type
                14 : type
                15 : {uint}
                16 : type
                17 : <unknown>
                18 : void
                19 : () -> void
                l0 : main::Web_Event
                l1 : <unknown>
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::UnknownDirective {
                        name: i.intern("foo"),
                    },
                    522..525,
                    None,
                )]
            },
        )
    }
}

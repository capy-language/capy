#![allow(clippy::uninlined_format_args)]
#![allow(clippy::too_many_arguments)]

mod globals;

#[cfg(test)]
mod tests;

use std::str::FromStr;

use debug::debug;
use globals::{ExprExpected, GlobalInferenceCtx};
use hir::{WorldBodies, common::*};
use interner::{Interner, Key};
use internment::Intern;
use itertools::Itertools;
use la_arena::{Arena, ArenaMap, Idx};

use rustc_hash::{FxHashMap, FxHashSet};
use text_size::TextRange;

use topo::TopoSort;

macro_rules! trait_alias {
    ($vis:vis $name:ident : $trait:path) => {
        $vis trait $name: $trait {}

        impl<T: $trait> $name for T {}
    };
}

pub(crate) use trait_alias;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NaiveLookupErr {
    /// If there's a generic function `add :: (comptime T: type, a: T, b: T) -> T {}` and the user
    /// references this as a first class expression `add`, then this will tell the compiler that this has happened.
    IsPolymorphic,
    NotFound,
}

/// `infer_expr` and `infer_stmt` will stop execution and return a list of Concrete Locations
/// to globals they come across that they don't immediately know.
///
/// The operator (`InferenceCtx::finish`) then handles making sure the dependencies of globals
/// are resolved before trying to rerun those original globals.
pub(crate) type InferResult<T> = Result<T, Vec<ConcreteLoc>>;

/// The final result returned from `hir_ty`
#[derive(Debug, Clone, Default)]
pub struct WorldTys {
    // The signature of a location is the type of that location
    // e.g.
    // ```
    // foo : i32 = 42;
    // ```
    // foo has a signature of i32
    // TODO: signatures only really have use when global
    signatures: FxHashMap<ConcreteLoc, Intern<Ty>>,
    // each concrete location corresponds to a type area.
    //
    // e.g. in the example above `foo` has the area including
    // 1. its type annotation, and
    // 2. the value "42"
    //
    // in this case:
    // ```
    // bar :: () {
    //  //..
    // };
    // ```
    //
    // `bar`s area includes the headers of the lambda,
    // and the lambda itself has an area which includes both the header (again)
    // and its entire body
    areas: FxHashMap<ConcreteLoc, AreaTys>,
}

impl WorldTys {
    #[track_caller]
    pub fn sig(&self, loc: ConcreteLoc) -> Intern<Ty> {
        self.signatures[&loc]
    }

    pub fn try_sig(&self, loc: ConcreteLoc) -> Option<Intern<Ty>> {
        self.signatures.get(&loc).copied()
    }

    pub fn try_naive(
        &self,
        naive: NaiveLoc,
        world_bodies: &WorldBodies,
    ) -> Result<Intern<Ty>, NaiveLookupErr> {
        if let Some(sig) = self.signatures.get(&naive.make_concrete(None)) {
            return Ok(*sig);
        }

        if world_bodies.has_polymorphic_body(naive) {
            return Err(NaiveLookupErr::IsPolymorphic);
        }

        for loc in self.signatures.keys() {
            if loc.to_naive() == naive {
                return Err(NaiveLookupErr::IsPolymorphic);
            }
        }

        Err(NaiveLookupErr::NotFound)
    }

    pub fn create_area_if_not_exists(&mut self, loc: ConcreteLoc) -> &mut AreaTys {
        self.areas.entry(loc).or_default()
    }

    pub fn remove_area(&mut self, loc: ConcreteLoc) {
        self.areas.remove(&loc);
    }

    pub fn has_area(&self, loc: ConcreteLoc) -> bool {
        self.areas.contains_key(&loc)
    }
}

impl std::ops::Index<ConcreteLoc> for WorldTys {
    type Output = AreaTys;

    #[track_caller]
    fn index(&self, loc: ConcreteLoc) -> &Self::Output {
        match self.areas.get(&loc) {
            Some(area) => area,
            None => panic!("the location {loc:?} does not have an area"),
        }
    }
}

impl std::ops::IndexMut<ConcreteLoc> for WorldTys {
    #[track_caller]
    fn index_mut(&mut self, loc: ConcreteLoc) -> &mut Self::Output {
        match self.areas.get_mut(&loc) {
            Some(area) => area,
            None => panic!("the location {loc:?} does not have an area"),
        }
    }
}

// The inference of expressions and statements within a global or function body
#[derive(Debug, Clone, Default)]
pub struct AreaTys {
    expr_tys: ArenaMap<Idx<hir::Expr>, Intern<Ty>>,
    /// the actual types of type expressions
    meta_tys: ArenaMap<Idx<hir::Expr>, Intern<Ty>>,
    local_tys: ArenaMap<Idx<hir::LocalDef>, Intern<Ty>>,
    switch_local_tys: ArenaMap<Idx<hir::SwitchArg>, Intern<Ty>>,
}

impl AreaTys {
    pub fn meta_ty(&self, expr: Idx<hir::Expr>) -> Option<Intern<Ty>> {
        self.meta_tys.get(expr).copied()
    }

    pub fn try_get_expr(&self, expr: Idx<hir::Expr>) -> Option<Intern<Ty>> {
        self.expr_tys.get(expr).copied()
    }
}

impl std::ops::Index<Idx<hir::Expr>> for AreaTys {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        match self.expr_tys.get(expr) {
            Some(ty) => ty,
            None => panic!("expr #{} was not given a type", expr.into_raw()),
        }
    }
}

impl std::ops::IndexMut<Idx<hir::Expr>> for AreaTys {
    #[track_caller]
    fn index_mut(&mut self, expr: Idx<hir::Expr>) -> &mut Self::Output {
        match self.expr_tys.get_mut(expr) {
            Some(ty) => ty,
            None => panic!("expr #{} was not given a type", expr.into_raw()),
        }
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for AreaTys {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, local_def: Idx<hir::LocalDef>) -> &Self::Output {
        &self.local_tys[local_def]
    }
}

impl std::ops::Index<Idx<hir::SwitchArg>> for AreaTys {
    type Output = Intern<Ty>;

    #[track_caller]
    fn index(&self, switch_local: Idx<hir::SwitchArg>) -> &Self::Output {
        &self.switch_local_tys[switch_local]
    }
}

pub trait LocationResolver {
    /// Returns None if the given location is a global that does
    /// not contain a lambda body.
    ///
    /// TODO: How does this work with aliased functions?
    /// e.g.
    /// ```text
    /// add :: () {}
    /// foo :: add;
    /// ```
    ///
    /// TODO: maybe just check the signature of the global and take the
    /// `fn_loc` from `ConcreteFn`
    fn resolve_to_lambda(
        self,
        world_bodies: &WorldBodies,
        tys: &WorldTys,
        interner: &Interner,
    ) -> Option<ConcreteLambdaLoc>;
}

impl LocationResolver for ConcreteGlobalLoc {
    fn resolve_to_lambda(
        self,
        world_bodies: &WorldBodies,
        tys: &WorldTys,
        interner: &Interner,
    ) -> Option<ConcreteLambdaLoc> {
        let body = world_bodies.global_body(self.to_naive());

        let hir::Expr::Lambda(lambda) = world_bodies[self.file()][body] else {
            return None;
        };

        let lambda_loc = NaiveLambdaLoc {
            file: self.file(),
            expr: body,
            lambda,
        }
        .make_concrete(self.comptime_args());

        // This just checks that the lambda exists.
        // TODO: this is the only use I found for giving lambdas
        // signatures. I'm thinking that maybe it's unnecessary.
        // The same check could be done by checking for an existing
        // area as opposed to an existing signature.
        // Maybe signatures should only be for globals.
        // And maybe even just naive globals.
        assert!(
            tys.try_sig(lambda_loc.wrap()).is_some(),
            "{} exists but {} doesn't for some reason",
            self.debug(interner),
            lambda_loc.debug(interner),
        );

        Some(lambda_loc)
    }
}

impl LocationResolver for ConcreteLoc {
    fn resolve_to_lambda(
        self,
        world_bodies: &WorldBodies,
        tys: &WorldTys,
        interner: &Interner,
    ) -> Option<ConcreteLambdaLoc> {
        match self {
            ConcreteLoc::Global(global) => global.resolve_to_lambda(world_bodies, tys, interner),
            ConcreteLoc::Lambda(lambda) => Some(lambda),
        }
    }
}

#[cfg(test)]
use derivative::Derivative;

#[derive(Clone)]
#[cfg_attr(not(test), derive(Debug, PartialEq))]
#[cfg_attr(test, derive(Derivative))]
#[cfg_attr(test, derivative(Debug, PartialEq))]
pub struct TyDiagnostic {
    pub kind: TyDiagnosticKind,
    pub file: FileName,
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
        fqn: Fqn,
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
        fqn: Fqn,
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
    FunctionTypeWithComptimeParameters,
    ComptimeArgNotConst {
        param_name: Key,
        param_ty: Intern<Ty>,
    },
    ArraySizeNotConst,
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

trait_alias! {
    pub EvalComptimeFn:
    FnMut(ComptimeLoc, &WorldTys) -> ComptimeResult
}

pub struct InferenceResult {
    pub tys: WorldTys,
    pub diagnostics: Vec<TyDiagnostic>,
    pub any_were_unsafe_to_compile: bool,
}

pub struct InferenceCtx<'a, F: EvalComptimeFn> {
    world_index: &'a hir::WorldIndex,
    world_bodies: &'a hir::WorldBodies,
    interner: &'a Interner,
    tys: WorldTys,
    all_finished_locations: FxHashSet<ConcreteLoc>,
    to_infer: TopoSort<ConcreteLoc>,
    generics_arena: &'a mut Arena<ComptimeResult>,
    call_associated_generics: FxHashMap<(ConcreteLoc, Idx<hir::Expr>), ComptimeArgs>,
    inferred_stmts: FxHashSet<(ConcreteLoc, Idx<hir::Stmt>)>,
    diagnostics: Vec<TyDiagnostic>,
    eval_comptime: F,
}

impl<'a, F: EvalComptimeFn> InferenceCtx<'a, F> {
    pub fn new(
        world_index: &'a hir::WorldIndex,
        world_bodies: &'a hir::WorldBodies,
        interner: &'a Interner,
        generics_arena: &'a mut Arena<ComptimeResult>,
        eval_comptime: F,
    ) -> Self {
        Self {
            world_index,
            world_bodies,
            interner,
            generics_arena,
            call_associated_generics: Default::default(),
            diagnostics: Default::default(),
            tys: Default::default(),
            all_finished_locations: Default::default(),
            to_infer: Default::default(),
            inferred_stmts: Default::default(),
            eval_comptime,
        }
    }

    /// only pass `None` to `entry_point` if your testing type checking and you don't want to worry
    /// about the entry point
    pub fn finish(
        mut self,
        entry_point: Option<NaiveGlobalLoc>,
        track_unsafe_to_compile: bool,
    ) -> InferenceResult {
        // for (module, _) in self.world_index.get_all_files() {
        //     self.tys.globals.insert(module, GlobalInference::default());
        // }

        self.to_infer.extend(
            self.world_index
                .get_all_files()
                .into_iter()
                .flat_map(|(file, index)| {
                    index
                        .definitions()
                        .map(|name| Fqn { file, name }.wrap())
                        .filter(|naive_loc| !self.world_bodies.has_polymorphic_body(*naive_loc))
                        .map(|naive_loc| naive_loc.make_concrete(None))
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

        loop {
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

                    // I'm doing a custom sort here because the implementation of sort I chose
                    // will cause lots of incorrect circular definition errors.
                    // It seems to be because the cyclic globals need to be run
                    // before the cyclic lambdas are run.
                    cyclic.sort_by(|left, right| match (left, right) {
                        (ConcreteLoc::Global(l_global), ConcreteLoc::Global(r_global)) => {
                            l_global.cmp(r_global)
                        }
                        (ConcreteLoc::Lambda(l_lambda), ConcreteLoc::Lambda(r_lambda)) => {
                            l_lambda.cmp(r_lambda)
                        }
                        (ConcreteLoc::Global(_), ConcreteLoc::Lambda(_)) => {
                            std::cmp::Ordering::Less
                        }
                        (ConcreteLoc::Lambda(_), ConcreteLoc::Global(_)) => {
                            std::cmp::Ordering::Greater
                        }
                    });

                    let nyr = Ty::NotYetResolved.into();

                    let mut res = format!("!!!! CYCLIC !!!!");
                    for def_loc in &cyclic {
                        res.push_str(&format!("\n- {}", def_loc.debug(self.interner)));
                        if let ConcreteLoc::Global(_) = def_loc {
                            self.tys.signatures.insert(*def_loc, nyr);
                        }
                    }
                    debug!("{}", &res);

                    cyclic
                }
            };

            assert!(!leaves.is_empty());

            // println!("inferring leaves: {leaves:#?}");

            for inferrable in leaves {
                debug!(
                    "--- ATTEMPING TO TYPE {} ---",
                    inferrable.debug(self.interner)
                );

                // println!(" + {}", inferrable.debug(self.interner));
                match self.infer(inferrable) {
                    Ok(_) => {
                        debug!(
                            "--- FINISHED TYPING {} ---",
                            inferrable.debug(self.interner)
                        );
                        self.to_infer.remove(&inferrable);
                    }
                    Err(deps) => {
                        // println!(" - requires deps");
                        self.to_infer.insert_deps(inferrable, deps);
                    }
                }
            }

            // println!("\nsignatures -");
            // for (loc, sig) in &self.tys.signatures {
            //     println!(
            //         "{} : {}",
            //         loc.debug(self.interner),
            //         sig.simple_display(self.interner, false)
            //     );
            // }
            // println!();

            if self.to_infer.is_empty() {
                break;
            }
        }

        let mut any_were_unsafe_to_compile = false;

        if track_unsafe_to_compile {
            for todo_loc in self.all_finished_locations.clone().into_iter() {
                let is_extern = match todo_loc {
                    ConcreteLoc::Global(global) => {
                        self.world_bodies.global_is_extern(global.to_naive())
                    }
                    ConcreteLoc::Lambda(lambda) => {
                        if let Some(global) = get_naive_lambda_global(lambda.to_naive()) {
                            self.world_bodies.global_is_extern(global)
                        } else {
                            false
                        }
                    }
                };
                if is_extern {
                    continue;
                }

                let mut global_ctx = GlobalInferenceCtx {
                    loc: todo_loc,
                    world_index: self.world_index,
                    world_bodies: self.world_bodies,
                    bodies: &self.world_bodies[todo_loc.file()],
                    interner: self.interner,
                    expected_tys: Default::default(),
                    local_usages: Default::default(),
                    generics_arena: self.generics_arena,
                    call_associated_generics: &mut self.call_associated_generics,
                    tys: &mut self.tys,
                    param_tys: Vec::new(),
                    inline_comptime_args: Vec::new(),
                    inline_comptime_tys: Vec::new(),
                    all_finished_locations: &self.all_finished_locations,
                    inferred_stmts: &mut self.inferred_stmts,
                    to_infer: &mut self.to_infer,
                    diagnostics: &mut self.diagnostics,
                    eval_comptime: &mut self.eval_comptime,
                };

                match todo_loc {
                    ConcreteLoc::Global(global) => {
                        let body = self.world_bodies.global_body(global.to_naive());
                        let ty = self.world_bodies.global_ty(global.to_naive());

                        if !global_ctx.is_safe_to_compile(todo_loc, body).unwrap()
                            || ty.is_some_and(|ty| {
                                !global_ctx.is_safe_to_compile(todo_loc, ty).unwrap()
                            })
                        {
                            debug!("{} is unsafe to compile", todo_loc.debug(self.interner));
                            any_were_unsafe_to_compile = true;
                        }
                    }
                    ConcreteLoc::Lambda(lambda) => {
                        if !global_ctx
                            .is_safe_to_compile(todo_loc, lambda.expr())
                            .unwrap()
                        {
                            debug!("{} is unsafe to compile", todo_loc.debug(self.interner));
                            any_were_unsafe_to_compile = true;
                        }
                    }
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

                assert!(!self.world_bodies.has_polymorphic_body(entry_point.wrap()));
                let loc = entry_point.make_concrete(None).wrap();

                let ty = self.tys.sig(loc);

                if let Some((param_tys, return_ty)) = ty.as_function() {
                    let lambda = match self.world_bodies[entry_point.file]
                        [self.world_bodies.global_body(entry_point)]
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

    fn infer(&mut self, loc: ConcreteLoc) -> InferResult<()> {
        if self.all_finished_locations.contains(&loc) {
            return Ok(());
        }

        match loc {
            ConcreteLoc::Global(global) => self.infer_global(global)?,
            ConcreteLoc::Lambda(lambda) => self.infer_lambda(lambda)?,
        }

        self.all_finished_locations.insert(loc);

        Ok(())
    }

    fn infer_global(&mut self, global: ConcreteGlobalLoc) -> InferResult<()> {
        // make sure we didn't accidentally send a generic function to be inferred as an ungeneric function
        if global.comptime_args().is_none() {
            assert!(
                !self
                    .world_bodies
                    .has_polymorphic_body(global.to_naive().wrap())
            );
        }

        let mut global_ctx = GlobalInferenceCtx {
            loc: global.wrap(),
            world_index: self.world_index,
            world_bodies: self.world_bodies,
            bodies: &self.world_bodies[global.file()],
            interner: self.interner,
            expected_tys: Default::default(),
            local_usages: Default::default(),
            generics_arena: &mut self.generics_arena,
            call_associated_generics: &mut self.call_associated_generics,
            inferred_stmts: &mut self.inferred_stmts,
            tys: &mut self.tys,
            param_tys: Default::default(),
            inline_comptime_args: Vec::new(),
            inline_comptime_tys: Vec::new(),
            all_finished_locations: &self.all_finished_locations,
            to_infer: &mut self.to_infer,
            diagnostics: &mut self.diagnostics,
            eval_comptime: &mut self.eval_comptime,
        };

        let had_previous = global_ctx.tys.signatures.contains_key(&global.wrap());

        // TODO: I think had_previous is impossible

        if !had_previous {
            // we do this before parsing the possible type annotation to avoid a recursion like this:
            // a : a : 5;
            global_ctx
                .tys
                .signatures
                .insert(global.wrap(), Ty::NotYetResolved.into());
        }

        global_ctx.tys.create_area_if_not_exists(global.wrap());

        let ty_annotation = match self.world_bodies.global_ty(global.to_naive()) {
            Some(ty_expr) => match global_ctx.const_ty(ty_expr) {
                Ok(ty) => Some(ExprExpected {
                    expected_ty: ty,
                    annotation_range: global_ctx.bodies.range_for_expr(ty_expr),
                    is_return_ty: false,
                    is_default: false,
                }),
                Err(why) => {
                    global_ctx.tys.signatures.remove(&global.wrap());
                    return Err(why);
                }
            },
            None => None,
        };

        if self.world_bodies.global_is_extern(global.to_naive()) {
            let ty_annotation = match ty_annotation {
                Some(expected) => expected.expected_ty,
                None => {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ExternGlobalMissingTy,
                        file: global.file(),
                        expr: None,
                        range: self.world_index.range_info(global.to_naive()).whole,
                        help: None,
                    });

                    Ty::Unknown.into()
                }
            };

            self.tys.signatures.insert(global.wrap(), ty_annotation);

            return Ok(());
        }

        let body = self.world_bodies.global_body(global.to_naive());

        // we don't need to do anything fancy to allow recursion.
        // the `infer_surface` stage should have already figured out the
        // signature of every function, including this one.

        let ty = match global_ctx.finish_body(body, ty_annotation, true) {
            Ok(ty) => ty,
            Err(why) => {
                global_ctx.tys.signatures.remove(&global.wrap());
                return Err(why);
            }
        };

        self.tys.signatures.insert(global.wrap(), ty);

        Ok(())
    }

    fn infer_lambda(&mut self, lambda_loc: ConcreteLambdaLoc) -> InferResult<()> {
        let hir::Lambda {
            body,
            return_ty: return_ty_expr,
            params_range,
            ..
        } = self.world_bodies[lambda_loc.file()][lambda_loc.lambda()];

        // debug!("trying to load {}...", lambda_loc.debug(self.interner));
        let fn_type = self.tys[lambda_loc.wrap()][lambda_loc.expr()];

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
                        file: lambda_loc.file(),
                        expr: Some(lambda_loc.expr()),
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
                        file: lambda_loc.file(),
                        expr: Some(lambda_loc.expr()),
                        range: self.world_bodies[lambda_loc.file()]
                            .range_for_expr(lambda_loc.expr()),
                        help: None,
                    });
                }
            }
            hir::LambdaBody::Block(block) => {
                // todo: does this range look good?
                let return_ty_range = return_ty_expr
                    .map(|return_ty_expr| {
                        self.world_bodies[lambda_loc.file()].range_for_expr(return_ty_expr)
                    })
                    .unwrap_or_else(|| TextRange::new(params_range.end(), params_range.end()));

                let (param_tys, return_ty) = fn_type.as_function().unwrap();

                let mut global_ctx = GlobalInferenceCtx {
                    loc: lambda_loc.wrap(),
                    world_index: self.world_index,
                    world_bodies: self.world_bodies,
                    bodies: &self.world_bodies[lambda_loc.file()],
                    interner: self.interner,
                    expected_tys: Default::default(),
                    local_usages: Default::default(),
                    generics_arena: &mut self.generics_arena,
                    call_associated_generics: &mut self.call_associated_generics,
                    inferred_stmts: &mut self.inferred_stmts,
                    tys: &mut self.tys,
                    param_tys,
                    inline_comptime_args: Vec::new(),
                    inline_comptime_tys: Vec::new(),
                    all_finished_locations: &self.all_finished_locations,
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

                self.tys.signatures.insert(
                    lambda_loc.wrap(),
                    self.tys[lambda_loc.wrap()][lambda_loc.expr()],
                );
            }
        }

        Ok(())
    }
}

impl WorldTys {
    /// This might be slightly superficial in some scenarios, I'm not sure
    pub fn all_tys(&self) -> impl Iterator<Item = Intern<Ty>> + '_ {
        self.signatures
            .values()
            .copied()
            .chain(self.areas.values().flat_map(|tys| {
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
            areas: globals,
        } = self;
        signatures.shrink_to_fit();
        globals.shrink_to_fit();
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
            .filter(|(cloc, _)| include_mods || !cloc.file().is_mod(mod_dir, interner))
            // if the global has a signature AND inner expression types, we will display it later
            // TODO! do globals with signatures but without inner expression types even exist?
            .filter(|(cloc, _)| !self.areas.contains_key(cloc))
            .collect::<Vec<_>>();

        signatures.sort_by(|(fqn1, _), (fqn2, _)| fqn1.cmp(fqn2));

        for (cloc, ty) in signatures {
            s.push_str(&cloc.to_string(mod_dir, interner));
            s.push_str(" : ");
            s.push_str(&format!("{}\n", ty.display(mod_dir, interner, true)));
        }

        let mut globals = self
            .areas
            .iter()
            .filter(|(cloc, _)| include_mods || !cloc.file().is_mod(mod_dir, interner))
            .collect::<Vec<_>>();
        globals.sort_by_key(|(cloc, _)| **cloc);

        for (cloc, tys) in globals {
            let ty = self.try_sig(*cloc);

            // display the global name & type
            s.push_str(&cloc.to_string(mod_dir, interner));
            s.push_str(" : ");
            match ty {
                Some(ty) => s.push_str(&ty.display(mod_dir, interner, true).to_string()),
                None => s.push('?'),
            }
            s.push('\n');

            // display the global's inner expression types
            for (expr_idx, ty) in tys.expr_tys.iter() {
                if fancy {
                    s.push_str(&format!("  \x1B[90m#{}\x1B[0m", expr_idx.into_raw(),));
                } else {
                    if self.areas.len() > 1 {
                        s.push_str("  ");
                    }
                    s.push_str(&format!("{}", expr_idx.into_raw(),));
                }
                s.push_str(&format!(" : {}\n", ty.display(mod_dir, interner, true)));
            }

            for (local_def_idx, ty) in tys.local_tys.iter() {
                if fancy || self.areas.len() > 1 {
                    s.push_str("  ");
                }
                s.push_str(&format!(
                    "l{} : {}\n",
                    local_def_idx.into_raw(),
                    ty.display(mod_dir, interner, true)
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
            BuiltinKind::PtrToRaw { opt } => Ty::FunctionPointer {
                param_tys: if opt {
                    vec![ParamTy {
                        ty: Ty::Optional {
                            sub_ty: Ty::RawPtr { mutable: false }.into(),
                        }
                        .into(),
                        comptime: None,
                        varargs: false,
                        impossible_to_differentiate: false,
                    }]
                } else {
                    vec![ParamTy {
                        ty: Ty::RawPtr { mutable: false }.into(),
                        comptime: None,
                        varargs: false,
                        impossible_to_differentiate: false,
                    }]
                },
                return_ty: Ty::UInt(u8::MAX).into(),
            }
            .into(),
            BuiltinKind::PtrFromRaw { mutable, opt } => Ty::FunctionPointer {
                param_tys: vec![ParamTy {
                    ty: Ty::UInt(u8::MAX).into(),
                    comptime: None,
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
            BuiltinKind::MetaToRaw => Ty::FunctionPointer {
                param_tys: vec![ParamTy {
                    ty: Ty::Type.into(),
                    comptime: None,
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
                            name: Name(Key::size()),
                            ty: Ty::UInt(u8::MAX).into(),
                        },
                        MemberTy {
                            name: Name(Key::align()),
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
                        name: Name(Key::size()),
                        ty: Ty::UInt(u8::MAX).into(),
                    },
                    MemberTy {
                        name: Name(Key::align()),
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
                                name: Name(Key::len()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                            MemberTy {
                                name: Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                        ],
                        BuiltinSubKind::Slice => vec![MemberTy {
                            name: Name(Key::sub_ty()),
                            ty: Ty::Type.into(),
                        }],
                        BuiltinSubKind::Pointer => vec![
                            MemberTy {
                                name: Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: Name(Key::mutable()),
                                ty: Ty::Bool.into(),
                            },
                        ],
                        BuiltinSubKind::Distinct => vec![MemberTy {
                            name: Name(Key::sub_ty()),
                            ty: Ty::Type.into(),
                        }],
                        BuiltinSubKind::Struct => vec![MemberTy {
                            name: Name(Key::members()),
                            ty: Ty::Slice {
                                sub_ty: Ty::AnonStruct {
                                    members: vec![
                                        MemberTy {
                                            name: Name(Key::name()),
                                            ty: Ty::String.into(),
                                        },
                                        MemberTy {
                                            name: Name(Key::ty()),
                                            ty: Ty::Type.into(),
                                        },
                                        MemberTy {
                                            name: Name(Key::offset()),
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
                                name: Name(Key::variants()),
                                ty: Ty::Slice {
                                    sub_ty: Ty::Type.into(),
                                }
                                .into(),
                            },
                            MemberTy {
                                name: Name(Key::discriminant_offset()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                        ],
                        BuiltinSubKind::Variant => vec![
                            MemberTy {
                                name: Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: Name(Key::discriminant()),
                                ty: Ty::UInt(32).into(),
                            },
                        ],
                        BuiltinSubKind::Optional => vec![
                            MemberTy {
                                name: Name(Key::sub_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: Name(Key::is_non_zero()),
                                ty: Ty::Bool.into(),
                            },
                            MemberTy {
                                name: Name(Key::discriminant_offset()),
                                ty: Ty::UInt(u8::MAX).into(),
                            },
                        ],
                        BuiltinSubKind::ErrorUnion => vec![
                            MemberTy {
                                name: Name(Key::error_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: Name(Key::payload_ty()),
                                ty: Ty::Type.into(),
                            },
                            MemberTy {
                                name: Name(Key::discriminant_offset()),
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

mod cast;
mod ctx;

use hir::TyWithRange;
use interner::{Interner, Key};
use la_arena::{Arena, ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use text_size::TextRange;

#[derive(Clone)]
pub struct InferenceResult {
    signatures: FxHashMap<hir::Fqn, Signature>,
    modules: FxHashMap<hir::Name, ModuleInference>,
}

#[derive(Debug, Clone)]
pub struct ModuleInference {
    expr_tys: ArenaMap<Idx<hir::Expr>, ResolvedTy>,
    local_tys: ArenaMap<Idx<hir::LocalDef>, ResolvedTy>,
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub enum ResolvedTy {
    NotYetResolved,
    Unknown,
    /// a bit-width of u32::MAX represents an isize
    /// a bit-width of 0 represents ANY signed integer type
    IInt(u32),
    /// a bit-width of u32::MAX represents a usize
    /// a bit-width of 0 represents ANY unsigned integer type
    UInt(u32),
    /// the bit-width can either be 32 or 64
    /// a bit-width of 0 represents ANY float type
    Float(u32),
    Bool,
    String,
    Array {
        size: u64,
        sub_ty: Idx<ResolvedTy>,
    },
    Pointer {
        mutable: bool,
        sub_ty: Idx<ResolvedTy>,
    },
    Distinct {
        fqn: Option<hir::Fqn>,
        uid: u32,
        ty: Idx<ResolvedTy>,
    },
    Type,
    Void,
}

impl ResolvedTy {
    /// what it sounds like
    pub fn is_array(&self, resolved_arena: &Arena<ResolvedTy>) -> bool {
        match self {
            ResolvedTy::Array { .. } => true,
            ResolvedTy::Distinct { ty, .. } => resolved_arena[*ty].is_array(resolved_arena),
            _ => false,
        }
    }

    /// what it sounds like
    pub fn is_pointer(&self, resolved_arena: &Arena<ResolvedTy>) -> bool {
        match self {
            ResolvedTy::Pointer { .. } => true,
            ResolvedTy::Distinct { ty, .. } => resolved_arena[*ty].is_pointer(resolved_arena),
            _ => false,
        }
    }

    /// checks if `self` is a pointer, and returns the mutability and subtype if so
    pub fn get_pointer_semantics(
        self,
        resolved_arena: &Arena<ResolvedTy>,
    ) -> Option<(bool, ResolvedTy)> {
        match self {
            ResolvedTy::Pointer { mutable, sub_ty } => Some((mutable, resolved_arena[sub_ty])),
            ResolvedTy::Distinct { ty, .. } => {
                resolved_arena[ty].get_pointer_semantics(resolved_arena)
            }
            _ => None,
        }
    }

    /// returns true if the type is void, or contains void, or is an empty array, etc.
    pub fn is_empty(&self, resolved_arena: &Arena<ResolvedTy>) -> bool {
        match self {
            ResolvedTy::Void => true,
            ResolvedTy::Pointer { sub_ty, .. } => resolved_arena[*sub_ty].is_empty(resolved_arena),
            ResolvedTy::Array { size, sub_ty } => {
                *size == 0 || resolved_arena[*sub_ty].is_empty(resolved_arena)
            }
            ResolvedTy::Distinct { ty, .. } => resolved_arena[*ty].is_empty(resolved_arena),
            _ => false,
        }
    }

    /// returns true if the type is unknown, or contains unknown, or is an unknown array, etc.
    pub fn is_unknown(&self, resolved_arena: &Arena<ResolvedTy>) -> bool {
        match self {
            ResolvedTy::NotYetResolved => true,
            ResolvedTy::Unknown => true,
            ResolvedTy::Pointer { sub_ty, .. } => {
                resolved_arena[*sub_ty].is_unknown(resolved_arena)
            }
            ResolvedTy::Array { size, sub_ty } => {
                *size == 0 || resolved_arena[*sub_ty].is_unknown(resolved_arena)
            }
            ResolvedTy::Distinct { ty, .. } => resolved_arena[*ty].is_unknown(resolved_arena),
            _ => false,
        }
    }

    /// A true equality check
    pub fn is_equal_to(self, other: Self, resolved_arena: &Arena<ResolvedTy>) -> bool {
        if self == other {
            return true;
        }

        match (self, other) {
            (
                ResolvedTy::Array {
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Array {
                    size: second_size,
                    sub_ty: second_sub_ty,
                    ..
                },
            ) => {
                first_size == second_size
                    && resolved_arena[first_sub_ty]
                        .is_equal_to(resolved_arena[second_sub_ty], resolved_arena)
            }
            (
                ResolvedTy::Pointer {
                    mutable: first_mutable,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: second_mutable,
                    sub_ty: second_sub_ty,
                },
            ) => {
                first_mutable == second_mutable
                    && resolved_arena[first_sub_ty]
                        .is_equal_to(resolved_arena[second_sub_ty], resolved_arena)
            }
            (ResolvedTy::Distinct { uid: first, .. }, ResolvedTy::Distinct { uid: second, .. }) => {
                first == second
            }
            _ => false,
        }
    }

    /// an equality check that ignores distinct types.
    /// All other types must be exactly equal (i32 == i32, i32 != i64)
    pub fn is_functionally_equivalent_to(
        self,
        other: Self,
        resolved_arena: &Arena<ResolvedTy>,
    ) -> bool {
        if self == other {
            return true;
        }

        match (self, other) {
            (
                ResolvedTy::Array {
                    size: first_size,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Array {
                    size: second_size,
                    sub_ty: second_sub_ty,
                    ..
                },
            ) => {
                first_size == second_size
                    && resolved_arena[first_sub_ty].is_functionally_equivalent_to(
                        resolved_arena[second_sub_ty],
                        resolved_arena,
                    )
            }
            (
                ResolvedTy::Pointer {
                    mutable: first_mutable,
                    sub_ty: first_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: second_mutable,
                    sub_ty: second_sub_ty,
                },
            ) => {
                first_mutable == second_mutable
                    && resolved_arena[first_sub_ty].is_functionally_equivalent_to(
                        resolved_arena[second_sub_ty],
                        resolved_arena,
                    )
            }
            (ResolvedTy::Distinct { ty: first, .. }, ResolvedTy::Distinct { ty: second, .. }) => {
                resolved_arena[first]
                    .is_functionally_equivalent_to(resolved_arena[second], resolved_arena)
            }
            (ResolvedTy::Distinct { ty: distinct, .. }, other)
            | (other, ResolvedTy::Distinct { ty: distinct, .. }) => {
                // println!("  {:?} as {:?}", other, resolved_arena[distinct]);
                resolved_arena[distinct].is_functionally_equivalent_to(other, resolved_arena)
            }
            _ => false,
        }
    }

    /// checks if `self` is an array, and returns the size and subtype if so
    pub fn get_array_semantics(
        self,
        resolved_arena: &Arena<ResolvedTy>,
    ) -> Option<(u64, ResolvedTy)> {
        match self {
            ResolvedTy::Array { size, sub_ty } => Some((size, resolved_arena[sub_ty])),
            ResolvedTy::Distinct { ty, .. } => {
                resolved_arena[ty].get_array_semantics(resolved_arena)
            }
            _ => None,
        }
    }
}

impl std::ops::Index<hir::Fqn> for InferenceResult {
    type Output = Signature;

    fn index(&self, fqn: hir::Fqn) -> &Self::Output {
        &self.signatures[&fqn]
    }
}

impl std::ops::Index<hir::Name> for InferenceResult {
    type Output = ModuleInference;

    fn index(&self, module: hir::Name) -> &Self::Output {
        &self.modules[&module]
    }
}

impl std::ops::Index<Idx<hir::Expr>> for ModuleInference {
    type Output = ResolvedTy;

    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        &self.expr_tys[expr]
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for ModuleInference {
    type Output = ResolvedTy;

    fn index(&self, local_def: Idx<hir::LocalDef>) -> &Self::Output {
        &self.local_tys[local_def]
    }
}

#[derive(Debug, Clone)]
pub enum Signature {
    Function(FunctionSignature),
    Global(GlobalSignature),
}

impl Signature {
    pub fn as_function(&self) -> Option<&FunctionSignature> {
        match self {
            Signature::Function(signature) => Some(signature),
            Signature::Global(_) => None,
        }
    }

    pub fn as_global(&self) -> Option<&GlobalSignature> {
        match self {
            Signature::Function { .. } => None,
            Signature::Global(signature) => Some(signature),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub return_ty: ResolvedTy,
    pub param_tys: Vec<ResolvedTy>,
    pub is_extern: bool,
}

#[derive(Debug, Clone)]
pub struct GlobalSignature {
    pub ty: ResolvedTy,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TyDiagnostic {
    pub kind: TyDiagnosticKind,
    pub module: hir::Name,
    pub range: TextRange,
    pub help: Option<TyDiagnosticHelp>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyDiagnosticKind {
    Mismatch {
        expected: ResolvedTy,
        found: ResolvedTy,
    },
    Uncastable {
        from: ResolvedTy,
        to: ResolvedTy,
    },
    OpMismatch {
        op: hir::BinaryOp,
        first: ResolvedTy,
        second: ResolvedTy,
    },
    IfMismatch {
        found: ResolvedTy,
        expected: ResolvedTy,
    },
    IndexMismatch {
        found: ResolvedTy,
    },
    IndexOutOfBounds {
        index: u64,
        actual_size: u64,
        array_ty: ResolvedTy,
    },
    DerefMismatch {
        found: ResolvedTy,
    },
    MissingElse {
        expected: ResolvedTy,
    },
    MutateBinding,
    MutateImmutableRef,
    CannotMutate,
    MutableRefToImmutableData,
    Undefined {
        name: Key,
    },
    NotYetResolved {
        path: hir::Path,
    },
    ParamNotATy,
    MutableTy,
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
}

pub struct InferenceCtx<'a> {
    current_module: Option<hir::Name>,
    bodies_map: &'a FxHashMap<hir::Name, hir::Bodies>,
    world_index: &'a hir::WorldIndex,
    twr_arena: &'a Arena<TyWithRange>,
    resolved_arena: &'a mut Arena<ResolvedTy>,
    local_usages: ArenaMap<Idx<hir::LocalDef>, FxHashSet<LocalUsage>>,
    param_tys: Option<Vec<ResolvedTy>>,
    signatures: FxHashMap<hir::Fqn, Signature>,
    modules: FxHashMap<hir::Name, ModuleInference>,
    diagnostics: Vec<TyDiagnostic>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum LocalUsage {
    Def(Idx<hir::LocalDef>),
    Assign(Idx<hir::Assign>),
    Expr(Idx<hir::Expr>),
}

impl<'a> InferenceCtx<'a> {
    pub fn new(
        bodies_map: &'a FxHashMap<hir::Name, hir::Bodies>,
        world_index: &'a hir::WorldIndex,
        twr_arena: &'a Arena<TyWithRange>,
        resolved_arena: &'a mut Arena<ResolvedTy>,
    ) -> InferenceCtx<'a> {
        Self {
            current_module: None,
            bodies_map,
            world_index,
            twr_arena,
            resolved_arena,
            local_usages: ArenaMap::default(),
            param_tys: None,
            diagnostics: Vec::new(),
            signatures: FxHashMap::default(),
            modules: FxHashMap::default(),
        }
    }

    pub fn finish(mut self) -> (InferenceResult, Vec<TyDiagnostic>) {
        for (module, _) in self.world_index.get_all_modules() {
            self.modules.insert(
                module,
                ModuleInference {
                    expr_tys: ArenaMap::default(),
                    local_tys: ArenaMap::default(),
                },
            );
        }

        for (module, index) in self.world_index.get_all_modules() {
            for (name, global) in index.globals() {
                let fqn = hir::Fqn { module, name };

                #[allow(clippy::map_entry)]
                if !self.signatures.contains_key(&fqn) {
                    let global_sig = self.generate_global_signature(global, fqn);
                    self.signatures.insert(fqn, global_sig);
                }
            }

            for (name, function) in index.functions() {
                let fqn = hir::Fqn { module, name };

                #[allow(clippy::map_entry)]
                if !self.signatures.contains_key(&fqn) {
                    let fn_sig = self.generate_function_signature(function, fqn);
                    self.signatures.insert(fqn, fn_sig);
                }
            }
        }

        let mut result = InferenceResult {
            signatures: self.signatures,
            modules: self.modules,
        };
        result.shrink_to_fit();

        (result, self.diagnostics)
    }

    /// constructs the signature of a global only once, even though it might have many uses.
    /// saves much unneeded work
    fn singleton_global_signature(
        &mut self,
        global: &hir::Global,
        fqn: hir::Fqn,
    ) -> GlobalSignature {
        if let Some(sig) = self.signatures.get(&fqn) {
            return sig.as_global().unwrap().clone();
        }

        let sig = self.generate_global_signature(global, fqn);
        self.signatures.insert(fqn, sig);

        self.signatures[&fqn].as_global().unwrap().clone()
    }

    /// newly constructs the signature of a global every time it is called.
    /// please use `singleton_global_signature` instead
    fn generate_global_signature(&mut self, global: &hir::Global, fqn: hir::Fqn) -> Signature {
        let old_module = self.current_module;
        self.current_module = Some(fqn.module);
        // if the global has a type annotation (my_global : string : "hello"),
        // we must treat it differently than one that does not (my_global :: "hello")
        let sig = match global.ty {
            TyWithRange::Unknown => {
                self.signatures.insert(
                    fqn,
                    Signature::Global(GlobalSignature {
                        ty: ResolvedTy::NotYetResolved,
                    }),
                );

                let ty =
                    self.finish_body_unknown(self.bodies_map[&fqn.module].global(fqn.name), None);

                Signature::Global(GlobalSignature { ty })
            }
            ty_annotation => {
                let sig = Signature::Global(GlobalSignature {
                    ty: self.resolve_ty(ty_annotation),
                });

                self.signatures.insert(fqn, sig.clone());

                self.finish_body_known(
                    self.bodies_map[&fqn.module].global(fqn.name),
                    None,
                    sig.as_global().unwrap().ty,
                );

                sig
            }
        };

        self.current_module = old_module;

        sig
    }

    /// constructs the signature of a function only once, even though it might have many uses.
    /// saves much unneeded work
    fn singleton_fn_signature(
        &mut self,
        function: &hir::Function,
        fqn: hir::Fqn,
    ) -> FunctionSignature {
        if let Some(sig) = self.signatures.get(&fqn) {
            return sig.as_function().unwrap().clone();
        }

        let sig = self.generate_function_signature(function, fqn);

        sig.as_function().unwrap().clone()
    }

    /// newly constructs the signature of a function every time it is called.
    /// please use `singleton_fn_signature` instead
    fn generate_function_signature(
        &mut self,
        function: &hir::Function,
        fqn: hir::Fqn,
    ) -> Signature {
        let old_module = self.current_module;
        self.current_module = Some(fqn.module);

        let return_ty = self.resolve_ty(function.return_ty);

        let param_tys: Vec<_> = function
            .params
            .iter()
            .map(|param| self.resolve_ty(param.ty))
            .collect();

        let sig = Signature::Function(FunctionSignature {
            param_tys,
            return_ty,
            is_extern: function.is_extern,
        });

        self.signatures.insert(fqn, sig.clone());

        if !function.is_extern {
            let fn_sig = sig.as_function().unwrap();

            self.finish_body_known(
                self.bodies_map[&fqn.module].function_body(fqn.name),
                Some(fn_sig.param_tys.clone()),
                fn_sig.return_ty,
            );
        }

        self.current_module = old_module;

        sig
    }

    fn path_with_range_to_ty(&mut self, path: hir::PathWithRange) -> ResolvedTy {
        let (fqn, range) = match path {
            hir::PathWithRange::ThisModule { name, range } => (
                hir::Fqn {
                    module: self.current_module.expect("there is no current module"),
                    name,
                },
                range,
            ),
            hir::PathWithRange::OtherModule {
                fqn, name_range, ..
            } => (fqn, name_range),
        };

        match self.world_index.get_definition(fqn) {
            Ok(definition) => match definition {
                hir::Definition::Global(global) => {
                    let global_ty = self.singleton_global_signature(global, fqn).ty;

                    if global_ty == ResolvedTy::Unknown {
                        return ResolvedTy::Unknown;
                    }

                    if global_ty != ResolvedTy::Type {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::Mismatch {
                                expected: ResolvedTy::Type,
                                found: global_ty,
                            },
                            module: self.current_module.unwrap(),
                            range,
                            help: None,
                        });
                        return ResolvedTy::Unknown;
                    }

                    let global_body = self.bodies_map[&fqn.module].global(fqn.name);

                    let actual_ty = self.parse_expr_to_ty(global_body);

                    // parse the global body into a type
                    //match global_body {}

                    // give distinct types a name if they don't already have one

                    match actual_ty {
                        ResolvedTy::Distinct {
                            fqn: distinct_fqn,
                            uid,
                            ty: distinct_ty,
                        } if distinct_fqn.is_none() => ResolvedTy::Distinct {
                            fqn: Some(fqn),
                            uid,
                            ty: distinct_ty,
                        },
                        _ => actual_ty,
                    }
                }
                _ => todo!(),
            },
            Err(_) => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::Undefined { name: fqn.name.0 },
                    module: self.current_module.unwrap(),
                    range,
                    help: None,
                });
                ResolvedTy::Unknown
            }
        }
    }

    fn parse_expr_to_ty(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
        match &self.bodies_map[&self.current_module.unwrap()][expr] {
            hir::Expr::Missing => ResolvedTy::Unknown,
            hir::Expr::Ref { mutable, expr } => {
                let sub_ty = self.parse_expr_to_ty(*expr);

                ResolvedTy::Pointer {
                    mutable: *mutable,
                    sub_ty: self.resolved_arena.alloc(sub_ty),
                }
            }
            hir::Expr::Local(local_def) => {
                let local_ty = self.modules[&self.current_module.unwrap()].local_tys[*local_def];

                if local_ty == ResolvedTy::Unknown {
                    return ResolvedTy::Unknown;
                }

                if local_ty != ResolvedTy::Type {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::Type,
                            found: self.modules[&self.current_module.unwrap()].local_tys
                                [*local_def],
                        },
                        module: self.current_module.unwrap(),
                        range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                        help: None,
                    });

                    return ResolvedTy::Unknown;
                }

                let local_def = &self.bodies_map[&self.current_module.unwrap()][*local_def];

                if local_def.mutable {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::MutableTy,
                        module: self.current_module.unwrap(),
                        range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                        help: None,
                    });

                    return ResolvedTy::Unknown;
                }

                self.parse_expr_to_ty(local_def.value)
            }
            hir::Expr::Global(path) => self.path_with_range_to_ty(*path),
            hir::Expr::Param { .. } => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::ParamNotATy,
                    module: self.current_module.unwrap(),
                    range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                    help: None,
                });

                ResolvedTy::Unknown
            }
            hir::Expr::PrimitiveTy { ty } => self.resolve_ty(self.twr_arena[*ty]),
            _ => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::Type,
                        found: self.modules[&self.current_module.unwrap()].expr_tys[expr],
                    },
                    module: self.current_module.unwrap(),
                    range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                    help: None,
                });

                ResolvedTy::Unknown
            }
        }
    }

    fn resolve_ty(&mut self, ty: hir::TyWithRange) -> ResolvedTy {
        match ty {
            hir::TyWithRange::Unknown => ResolvedTy::Unknown,
            hir::TyWithRange::IInt { bit_width, .. } => ResolvedTy::IInt(bit_width),
            hir::TyWithRange::UInt { bit_width, .. } => ResolvedTy::UInt(bit_width),
            hir::TyWithRange::Float { bit_width, .. } => ResolvedTy::Float(bit_width),
            hir::TyWithRange::Bool { .. } => ResolvedTy::Bool,
            hir::TyWithRange::String { .. } => ResolvedTy::String,
            hir::TyWithRange::Array { size, sub_ty, .. } => ResolvedTy::Array {
                size,
                sub_ty: {
                    let ty = self.resolve_ty(self.twr_arena[sub_ty]);
                    self.resolved_arena.alloc(ty)
                },
            },
            hir::TyWithRange::Pointer {
                mutable, sub_ty, ..
            } => ResolvedTy::Pointer {
                mutable,
                sub_ty: {
                    let ty = self.resolve_ty(self.twr_arena[sub_ty]);
                    self.resolved_arena.alloc(ty)
                },
            },
            hir::TyWithRange::Distinct { uid, ty } => ResolvedTy::Distinct {
                fqn: None,
                uid,
                ty: {
                    let ty = self.resolve_ty(self.twr_arena[ty]);
                    self.resolved_arena.alloc(ty)
                },
            },
            hir::TyWithRange::Type { .. } => ResolvedTy::Type,
            hir::TyWithRange::Named { path } => self.path_with_range_to_ty(path),
            hir::TyWithRange::Void { .. } => ResolvedTy::Void,
        }
    }
}

impl InferenceResult {
    fn shrink_to_fit(&mut self) {
        let Self { signatures, .. } = self;
        signatures.shrink_to_fit();
        // expr_types.shrink_to_fit();
        // local_types.shrink_to_fit();
    }
}

impl InferenceResult {
    pub fn debug(
        &self,
        resolved_arena: &Arena<ResolvedTy>,
        interner: &Interner,
        fancy: bool,
    ) -> String {
        let mut s = String::new();

        let mut signatures = self.signatures.iter().collect::<Vec<_>>();

        signatures.sort_by_key(|(fqn, _)| {
            format!(
                "{}.{}",
                interner.lookup(fqn.module.0),
                interner.lookup(fqn.name.0)
            )
        });

        for (fqn, signature) in signatures {
            match signature {
                Signature::Function(FunctionSignature {
                    return_ty,
                    param_tys,
                    is_extern,
                }) => {
                    s.push_str(&format!(
                        "{}.{} : ",
                        interner.lookup(fqn.module.0),
                        interner.lookup(fqn.name.0)
                    ));

                    if *is_extern {
                        s.push_str("extern ");
                    }
                    s.push('(');
                    for (idx, param_type) in param_tys.iter().enumerate() {
                        if idx != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&param_type.display(resolved_arena, interner));
                    }
                    s.push(')');

                    s.push_str(&format!(
                        " -> {}\n",
                        return_ty.display(resolved_arena, interner)
                    ));
                }
                Signature::Global(GlobalSignature { ty }) => {
                    s.push_str(&format!(
                        "{}.{} : ",
                        interner.lookup(fqn.module.0),
                        interner.lookup(fqn.name.0)
                    ));
                    s.push_str(&format!("{}\n", ty.display(resolved_arena, interner)));
                }
            }
        }

        let mut modules = self.modules.iter().collect::<Vec<_>>();
        modules.sort_by_key(|(name, _)| interner.lookup(name.0));

        for (name, module) in modules {
            if fancy || self.modules.len() > 1 {
                s.push_str(&format!("{}:\n", interner.lookup(name.0)));
            }
            for (expr_idx, ty) in module.expr_tys.iter() {
                if fancy {
                    s.push_str(&format!("  \x1B[90m#{}\x1B[0m", expr_idx.into_raw(),));
                } else {
                    if self.modules.len() > 1 {
                        s.push_str("  ");
                    }
                    s.push_str(&format!("{}", expr_idx.into_raw(),));
                }
                s.push_str(&format!(" : {}\n", ty.display(resolved_arena, interner)));
            }

            for (local_def_idx, ty) in module.local_tys.iter() {
                if fancy || self.modules.len() > 1 {
                    s.push_str("  ");
                }
                s.push_str(&format!(
                    "l{} : {}\n",
                    local_def_idx.into_raw(),
                    ty.display(resolved_arena, interner)
                ));
            }
        }

        s
    }
}

impl ResolvedTy {
    pub fn display(&self, resolved_arena: &Arena<ResolvedTy>, interner: &Interner) -> String {
        match self {
            Self::NotYetResolved => "!".to_string(),
            Self::Unknown => "<unknown>".to_string(),
            Self::IInt(bit_width) => match *bit_width {
                u32::MAX => "isize".to_string(),
                0 => "{int}".to_string(),
                _ => format!("i{}", bit_width),
            },
            Self::UInt(bit_width) => match *bit_width {
                u32::MAX => "usize".to_string(),
                0 => "{uint}".to_string(),
                _ => format!("u{}", bit_width),
            },
            Self::Float(bit_width) => match *bit_width {
                0 => "{float}".to_string(),
                _ => format!("f{}", bit_width),
            },
            Self::Bool => "bool".to_string(),
            Self::String => "string".to_string(),
            Self::Array { size, sub_ty } => {
                format!(
                    "[{size}]{}",
                    resolved_arena[*sub_ty].display(resolved_arena, interner)
                )
            }
            Self::Pointer { mutable, sub_ty } => {
                format!(
                    "^{}{}",
                    if *mutable { "mut " } else { "" },
                    resolved_arena[*sub_ty].display(resolved_arena, interner)
                )
            }
            Self::Distinct { fqn, uid, ty } => match fqn {
                Some(fqn) => format!(
                    "{}.{}",
                    interner.lookup(fqn.module.0),
                    interner.lookup(fqn.name.0)
                ),
                None => format!(
                    "distinct'{} {}",
                    uid,
                    resolved_arena[*ty].display(resolved_arena, interner)
                ),
            },
            Self::Type => "type".to_string(),
            Self::Void => "void".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::AstNode;
    use expect_test::{expect, Expect};
    use hir::UIDGenerator;
    use interner::Interner;
    use la_arena::RawIdx;

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
        let modules = test_utils::split_multi_module_test_data(input);
        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        let mut uid_gen = UIDGenerator::default();
        let mut twr_arena = Arena::new();
        let mut bodies_map = FxHashMap::default();

        for (name, text) in &modules {
            if *name == "main" {
                continue;
            }

            let tokens = lexer::lex(text);
            let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, _) = hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

            let module = hir::Name(interner.intern(name));

            world_index.add_module(module, index);

            let (bodies, _) = hir::lower(
                root,
                &tree,
                module,
                &world_index,
                &mut uid_gen,
                &mut twr_arena,
                &mut interner,
            );
            bodies_map.insert(module, bodies);
        }

        let text = &modules["main"];
        let module = hir::Name(interner.intern("main"));
        let tokens = lexer::lex(text);
        let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);
        world_index.add_module(module, index);

        let (bodies, _) = hir::lower(
            root,
            &tree,
            module,
            &world_index,
            &mut uid_gen,
            &mut twr_arena,
            &mut interner,
        );
        bodies_map.insert(module, bodies);

        let mut resolved_arena = Arena::new();

        let (inference_result, actual_diagnostics) =
            InferenceCtx::new(&bodies_map, &world_index, &twr_arena, &mut resolved_arena).finish();

        expect.assert_eq(&inference_result.debug(&resolved_arena, &interner, false));

        let expected_diagnostics: Vec<_> = expected_diagnostics(&mut interner)
            .into_iter()
            .map(|(kind, range, help)| TyDiagnostic {
                kind,
                module,
                range: TextRange::new(range.start.into(), range.end.into()),
                help: help.map(|(kind, range)| TyDiagnosticHelp {
                    kind,
                    range: TextRange::new(range.start.into(), range.end.into()),
                }),
            })
            .collect();

        assert_eq!(expected_diagnostics, actual_diagnostics);
    }

    #[test]
    fn unit_function() {
        check(
            r#"
                foo :: () -> {};
            "#,
            expect![[r#"
                main.foo : () -> void
                0 : void
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
                main.one : () -> i32
                0 : i32
                1 : i32
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
                main.one : () -> f32
                0 : f32
                1 : f32
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
                main.one : () -> f32
                0 : f32
                1 : f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn functions_with_undefined_return_ty() {
        check(
            r#"
                one :: () -> foo {};
                two :: () -> bar.baz {};
            "#,
            expect![[r#"
                main.one : () -> <unknown>
                main.two : () -> <unknown>
                0 : void
                1 : void
            "#]],
            |i| {
                [
                    (
                        TyDiagnosticKind::Undefined {
                            name: i.intern("foo"),
                        },
                        30..33,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Undefined {
                            name: i.intern("baz"),
                        },
                        71..74,
                        None,
                    ),
                ]
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
                main.twenty : () -> u8
                0 : u8
                1 : u8
                2 : u8
                3 : u8
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_diff_types() {
        check(
            r#"
                calc :: () -> isize {
                    num1 := 4 as i128;
                    num2 := 8 as u16;
                    num1 + num2
                };
            "#,
            expect![[r#"
                main.calc : () -> isize
                0 : i128
                1 : i128
                2 : u16
                3 : u16
                4 : i128
                5 : u16
                6 : i128
                7 : i128
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
                    num1 := 4 as u16;
                    num1 + 8
                };
            "#,
            expect![[r#"
                main.calc : () -> u128
                0 : u16
                1 : u16
                2 : u16
                3 : u16
                4 : u16
                5 : u16
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
                main.calc : () -> i128
                0 : u16
                1 : u16
                2 : i128
                3 : i128
                4 : i128
                5 : i128
                l0 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::UInt(16),
                        second: ResolvedTy::IInt(0),
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
                    is_true := num as bool;
                    is_true
                };
            "#,
            expect![[r#"
                main.check : () -> bool
                0 : {uint}
                1 : {uint}
                2 : bool
                3 : bool
                4 : bool
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
                    age := name as usize;
                    age
                };
            "#,
            expect![[r#"
                main.how_old : () -> usize
                0 : string
                1 : string
                2 : usize
                3 : usize
                4 : usize
                l0 : string
                l1 : usize
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: ResolvedTy::String,
                        to: ResolvedTy::UInt(u32::MAX),
                    },
                    108..121,
                    None,
                )]
            },
        );
    }

    #[test]
    fn strong_int_to_float() {
        check(
            r#"
                main :: () -> {
                    foo : u16 = 5;

                    bar : f32 = foo;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : u16
                1 : u16
                2 : void
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
                main :: () -> {
                    foo : f32 = 5;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : f32
                1 : void
                l0 : f32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_float_and_float() {
        check(
            r#"
                main :: () -> {
                    foo : f32 = 5;
                    bar : f64 = 10;

                    foo + bar;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : f32
                1 : f64
                2 : f32
                3 : f64
                4 : f64
                5 : void
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
                main :: () -> {
                    foo : i32 = 5;
                    bar : f64 = 10;

                    foo + bar;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : i32
                1 : f64
                2 : i32
                3 : f64
                4 : f64
                5 : void
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
                main :: () -> {
                    foo : f64 = 10;

                    5 + foo;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : f64
                1 : f64
                2 : f64
                3 : f64
                4 : void
                l0 : f64
            "#]],
            |_| [],
        );
    }

    #[test]
    fn binary_expr_weak_int_and_weak_float() {
        check(
            r#"
                main :: () -> {
                    5 + 10.0;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {float}
                1 : {float}
                2 : {float}
                3 : void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn inference_simple_by_annotation() {
        check(
            r#"
                main :: () -> {
                    num1 := 5;
                    num2 := num1;
                    num3 : usize = num2;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : usize
                1 : usize
                2 : usize
                3 : void
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
                main :: () -> {
                    my_array := [] i32 { 4, 8, 15, 16, 23, 42 };
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : [6]i32
                7 : void
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_with_size() {
        check(
            r#"
                main :: () -> {
                    my_array := [6] i32 { 4, 8, 15, 16, 23, 42 };
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : [6]i32
                7 : void
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_with_incorrect_size() {
        check(
            r#"
                main :: () -> {
                    my_array := [7] i32 { 4, 8, 15, 16, 23, 42 };
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : [7]i32
                7 : void
                l0 : [7]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn index() {
        check(
            r#"
                main :: () -> i32 {
                    my_array := [] i32 { 4, 8, 15, 16, 23, 42 };

                    my_array[2]
                };
            "#,
            expect![[r#"
                main.main : () -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : [6]i32
                7 : [6]i32
                8 : usize
                9 : i32
                10 : i32
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
                    my_array := [] i32 { 4, 8, 15, 16, 23, 42 };

                    my_array[1000]
                };
            "#,
            expect![[r#"
                main.main : () -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : [6]i32
                7 : [6]i32
                8 : usize
                9 : i32
                10 : i32
                l0 : [6]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexOutOfBounds {
                        index: 1000,
                        actual_size: 6,
                        array_ty: ResolvedTy::Array {
                            size: 6,
                            sub_ty: Idx::from_raw(RawIdx::from(0)),
                        },
                    },
                    123..137,
                    None,
                )]
            },
        );
    }

    #[test]
    fn inference_complex_by_annotation() {
        check(
            r#"
                main :: () -> {
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
                main.main : () -> void
                0 : i16
                1 : bool
                2 : i16
                3 : i16
                4 : i16
                5 : i16
                6 : i16
                7 : i16
                8 : i16
                9 : void
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
                main.main : () -> usize
                0 : usize
                1 : usize
                2 : usize
                3 : usize
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
                main.main : () -> i8
                0 : i8
                1 : bool
                2 : i8
                3 : i8
                4 : i8
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : i8
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
                main.main : () -> u8
                0 : u8
                1 : bool
                2 : u8
                3 : u8
                4 : u8
                5 : u8
                6 : u8
                7 : u8
                8 : u8
                9 : u8
                10 : u8
                l0 : u8
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::IInt(0),
                    },
                    300..303,
                    None,
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
                main.add : (i32, i32) -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_definition_and_usage() {
        check(
            r#"
                main :: () -> {
                    a := 10;
                    a;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : void
                l0 : {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn local_shadowing() {
        check(
            r#"
                foo :: () -> {
                    a := 10;
                    a := "10";
                    a;
                };
            "#,
            expect![[r#"
                main.foo : () -> void
                0 : {uint}
                1 : string
                2 : string
                3 : void
                l0 : {uint}
                l1 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign() {
        check(
            r#"
                foo :: () -> {
                    a := "Hello";
                    a = "World"; // `a` on the left is an expression, and it's type is evaluated
                    a;
                };
            "#,
            expect![[r#"
                main.foo : () -> void
                0 : string
                1 : string
                2 : string
                3 : string
                4 : void
                l0 : string
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
                main.foo : () -> i16
                0 : i8
                1 : i8
                2 : i16
                3 : i16
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
                main.foo : () -> u8
                0 : u16
                1 : u16
                2 : u8
                3 : u8
                l0 : u16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::UInt(16),
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
                main.foo : () -> i16
                0 : u8
                1 : u8
                2 : i16
                3 : i16
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
                main.foo : () -> u16
                0 : i8
                1 : i8
                2 : u16
                3 : u16
                l0 : i8
                l1 : u16
            "#]],
            |_| {
                // should fail due to loss of sign
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(16),
                        found: ResolvedTy::IInt(8),
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
                main.foo : () -> u16
                0 : i16
                1 : i16
                2 : u16
                3 : u16
                l0 : i16
                l1 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(16),
                        found: ResolvedTy::IInt(16),
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
                main.foo : () -> u8
                0 : i16
                1 : i16
                2 : u8
                3 : u8
                l0 : i16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::IInt(16),
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
                main.sum : () -> i32
                0 : string
                1 : i32
                2 : i32
                3 : i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::String,
                        second: ResolvedTy::UInt(0),
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
                main.f : () -> i32
                0 : i32
                1 : <unknown>
                2 : i32
                3 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn invalid_binary_expr_with_missing_operand() {
        check(
            r#"
                f :: () -> string { "hello" + };
            "#,
            expect![[r#"
                main.f : () -> string
                0 : string
                1 : <unknown>
                2 : string
                3 : string
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
                main.f : () -> bool
                0 : bool
                1 : {uint}
                2 : bool
                3 : bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Lt,
                        first: ResolvedTy::Bool,
                        second: ResolvedTy::UInt(0),
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
                main.f : () -> bool
                0 : string
                1 : string
                2 : bool
                3 : bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::And,
                        first: ResolvedTy::String,
                        second: ResolvedTy::String,
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
                main.both : () -> bool
                0 : bool
                1 : bool
                2 : bool
                3 : bool
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
                main.either : () -> bool
                0 : bool
                1 : <unknown>
                2 : bool
                3 : bool
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
                main.less : () -> bool
                0 : {uint}
                1 : {uint}
                2 : bool
                3 : bool
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
                main.equality : () -> bool
                0 : {uint}
                1 : <unknown>
                2 : bool
                3 : bool
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
                main.redundant : () -> u8
                0 : u8
                1 : u8
                2 : u8
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
                main.neg : () -> u8
                0 : u8
                1 : u8
                2 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8),
                        found: ResolvedTy::IInt(0),
                    },
                    35..37,
                    None,
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
                main.pos : () -> i8
                0 : i8
                1 : i8
                2 : i8
                3 : i8
                4 : i8
                5 : i8
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
                main.not : () -> bool
                0 : bool
                1 : bool
                2 : bool
            "#]],
            |_| [],
        );
    }

    #[test]
    fn mismatched_function_body() {
        check(
            r#"
                s :: () -> string { 92 };
            "#,
            expect![[r#"
                main.s : () -> string
                0 : {uint}
                1 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::String,
                        found: ResolvedTy::UInt(0),
                    },
                    37..39,
                    None,
                )]
            },
        );
    }

    #[test]
    fn call_void_function() {
        check(
            r#"
                main :: () -> { nothing(); };
                nothing :: () -> {};
            "#,
            expect![[r#"
                main.main : () -> void
                main.nothing : () -> void
                0 : void
                1 : void
                2 : void
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
                main.main : () -> i32
                main.number : () -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
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
                main.id : (i32) -> i32
                main.main : () -> i32
                0 : i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
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
                main.main : () -> i32
                main.multiply : (i32, i32) -> i32
                0 : void
                1 : string
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::IInt(32),
                            found: ResolvedTy::Void,
                        },
                        46..48,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::IInt(32),
                            found: ResolvedTy::String,
                        },
                        50..53,
                        None,
                    ),
                ]
            },
        );
    }

    #[test]
    fn call_function_from_other_module() {
        check(
            r#"
                #- main
                a :: () -> string { greetings.informal(10) };
                #- greetings
                informal :: (n: i32) -> string { "Hello!" };
            "#,
            expect![[r#"
                greetings.informal : (i32) -> string
                main.a : () -> string
                greetings:
                  0 : string
                  1 : string
                main:
                  0 : i32
                  1 : string
                  2 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn attach_mismatch_diagnostics_to_block_tail_expr() {
        check(
            r#"
                main :: () -> {
                    take_i32({
                        a := 10 + 10;
                        "foo"
                    });
                };

                take_i32 :: (n: i32) {};
            "#,
            expect![[r#"
                main.main : () -> void
                main.take_i32 : (i32) -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : string
                4 : string
                5 : void
                6 : void
                7 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::IInt(32),
                        found: ResolvedTy::String,
                    },
                    126..131,
                    None,
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
                main.imaginary : type
                main.main : () -> i32
                0 : type
                1 : main.imaginary
                2 : main.imaginary
                3 : main.imaginary
                l0 : main.imaginary
            "#]],
            |interner| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::IInt(32),
                        found: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::Name(interner.intern("main")),
                                name: hir::Name(interner.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: Idx::from_raw(RawIdx::from(0)),
                        },
                    },
                    147..148,
                    None,
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
                main.imaginary : type
                main.main : () -> main.imaginary
                0 : type
                1 : main.imaginary
                2 : main.imaginary
                3 : main.imaginary
                4 : main.imaginary
                5 : main.imaginary
                l0 : main.imaginary
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
                main.imaginary : type
                main.main : () -> main.imaginary
                0 : type
                1 : main.imaginary
                2 : main.imaginary
                3 : main.imaginary
                4 : main.imaginary
                5 : main.imaginary
                l0 : main.imaginary
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
                main.imaginary : type
                main.main : () -> main.imaginary
                0 : type
                1 : main.imaginary
                2 : i32
                3 : main.imaginary
                4 : i32
                5 : main.imaginary
                6 : main.imaginary
                l0 : main.imaginary
                l1 : i32
            "#]],
            |interner| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::Name(interner.intern("main")),
                                name: hir::Name(interner.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: Idx::from_raw(RawIdx::from(1)),
                        },
                        second: ResolvedTy::IInt(32),
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
                main.extra_imaginary : type
                main.imaginary : type
                main.main : () -> main.imaginary
                0 : type
                1 : type
                2 : main.imaginary
                3 : main.extra_imaginary
                4 : main.imaginary
                5 : main.extra_imaginary
                6 : main.imaginary
                7 : main.imaginary
                l0 : main.imaginary
                l1 : main.extra_imaginary
            "#]],
            |interner| {
                [(
                    TyDiagnosticKind::OpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::Name(interner.intern("main")),
                                name: hir::Name(interner.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: Idx::from_raw(RawIdx::from(1)),
                        },
                        second: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::Name(interner.intern("main")),
                                name: hir::Name(interner.intern("extra_imaginary")),
                            }),
                            uid: 1,
                            ty: Idx::from_raw(RawIdx::from(2)),
                        },
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

                    {i as ^i32}^
                };
            "#,
            expect![[r#"
                main.main : () -> i32
                main.something_far_away : type
                0 : type
                1 : i32
                2 : main.something_far_away
                3 : main.something_far_away
                4 : ^i32
                5 : ^i32
                6 : i32
                7 : i32
                l0 : main.something_far_away
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

                    {x as ^imaginary}^
                };
            "#,
            expect![[r#"
                main.imaginary : type
                main.imaginary_far_away : type
                main.main : () -> main.imaginary
                0 : type
                1 : type
                2 : main.imaginary
                3 : main.imaginary
                4 : main.imaginary_far_away
                5 : main.imaginary_far_away
                6 : ^main.imaginary
                7 : ^main.imaginary
                8 : main.imaginary
                9 : main.imaginary
                l0 : main.imaginary
                l1 : main.imaginary_far_away
            "#]],
            |_| [],
        );
    }

    #[test]
    fn distinct_arrays() {
        check(
            r#"
                Vector3 :: distinct [3] i32;

                main :: () -> {
                    my_point : Vector3 = [] i32 { 4, 8, 15 };

                    x := my_point[0];
                    y := my_point[1];
                    z := my_point[2];
                };
            "#,
            expect![[r#"
                main.Vector3 : type
                main.main : () -> void
                0 : type
                1 : i32
                2 : i32
                3 : i32
                4 : [3]i32
                5 : main.Vector3
                6 : usize
                7 : i32
                8 : main.Vector3
                9 : usize
                10 : i32
                11 : main.Vector3
                12 : usize
                13 : i32
                14 : void
                l0 : main.Vector3
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
                main.main : () -> ^i32
                0 : i32
                1 : i32
                2 : ^i32
                3 : ^i32
                l0 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn recursive_definition() {
        check(
            r#"
                foo :: bar;

                bar :: foo;
            "#,
            expect![[r#"
                main.bar : <unknown>
                main.foo : <unknown>
                0 : <unknown>
                1 : <unknown>
            "#]],
            |interner| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        path: hir::Path::ThisModule(hir::Name(interner.intern("foo"))),
                    },
                    53..56,
                    None,
                )]
            },
        );
    }

    #[test]
    fn assign_var() {
        check(
            r#"
                main :: () -> {
                    foo := 5;

                    foo = 42;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : void
                l0 : {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_binding() {
        check(
            r#"
                main :: () -> {
                    foo :: 5;

                    foo = 42;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    84..92,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 53..61)),
                )]
            },
        );
    }

    #[test]
    fn assign_non_mut_ptr_to_var() {
        check(
            r#"
                main :: () -> {
                    foo := 5;
                    bar :: ^foo; 

                    bar^ = 42;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : ^{uint}
                4 : {uint}
                5 : {uint}
                6 : void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    118..127,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 90..94)),
                )]
            },
        );
    }

    #[test]
    fn assign_mut_ptr_to_var() {
        check(
            r#"
                main :: () -> {
                    foo := 5;
                    bar :: ^mut foo; 

                    bar^ = 42;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : ^mut {uint}
                4 : {uint}
                5 : {uint}
                6 : void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| [],
        );
    }

    #[test]
    fn assign_to_immutable_expr() {
        check(
            r#"
                main :: () -> {
                    2 + 2 = 5;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : void
            "#]],
            |_| [(TyDiagnosticKind::CannotMutate, 53..58, None)],
        );
    }

    #[test]
    fn assign_to_mut_ref_expr() {
        check(
            r#"
                main :: () -> {
                    {^mut 2}^ = 5;
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : ^mut {uint}
                2 : ^mut {uint}
                3 : {uint}
                4 : {uint}
                5 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    54..60,
                    Some((TyDiagnosticHelpKind::FoundToBeImmutable, 59..60)),
                )]
            },
        );
    }

    #[test]
    fn mut_ptr_to_binding() {
        check(
            r#"
                main :: () -> {
                    foo :: 5;
                    bar :: ^mut foo; 
                };
            "#,
            expect![[r#"
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^mut {uint}
                3 : void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    90..98,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 53..61)),
                )]
            },
        );
    }

    #[test]
    fn reinfer_usages() {
        check(
            r#"
                main :: () -> {
                    foo := 5;
                
                    baz := foo;
                
                    foo = foo + 1;
                
                    bar(foo);
                };
                
                bar :: (x: usize) -> {};
            "#,
            expect![[r#"
                main.bar : (usize) -> void
                main.main : () -> void
                0 : usize
                1 : usize
                2 : usize
                3 : usize
                4 : usize
                5 : usize
                6 : usize
                7 : void
                8 : void
                9 : void
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
                main :: () -> {
                    foo := 5;
                
                    bar(^mut foo);
                };
                
                bar :: (x: ^i32) -> {};
            "#,
            expect![[r#"
                main.bar : (^i32) -> void
                main.main : () -> void
                0 : i32
                1 : i32
                2 : ^i32
                3 : void
                4 : void
                5 : void
                l0 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn pass_immutable_ref_to_mut_ref() {
        check(
            r#"
                main :: () -> {
                    foo := 5;
                
                    bar(^foo);
                };
                
                bar :: (x: ^mut i32) -> {};
            "#,
            expect![[r#"
                main.bar : (^mut i32) -> void
                main.main : () -> void
                0 : {uint}
                1 : {uint}
                2 : ^{uint}
                3 : void
                4 : void
                5 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::Pointer {
                            mutable: true,
                            sub_ty: Idx::from_raw(RawIdx::from(0)),
                        },
                        found: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: Idx::from_raw(RawIdx::from(1)),
                        },
                    },
                    104..108,
                    None,
                )]
            },
        );
    }
}

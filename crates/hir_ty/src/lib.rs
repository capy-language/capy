mod ctx;
mod resolved_ty;

use hir::{NameWithRange, TyWithRange};
use interner::{Interner, Key};
use internment::Intern;
use la_arena::{Arena, ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use text_size::TextRange;

pub use resolved_ty::*;

#[derive(Clone)]
pub struct InferenceResult {
    signatures: FxHashMap<hir::Fqn, Signature>,
    modules: FxHashMap<hir::FileName, ModuleInference>,
}

#[derive(Debug, Clone)]
pub struct ModuleInference {
    expr_tys: ArenaMap<Idx<hir::Expr>, Intern<ResolvedTy>>,
    local_tys: ArenaMap<Idx<hir::LocalDef>, Intern<ResolvedTy>>,
    lambdas: ArenaMap<Idx<hir::Lambda>, FunctionSignature>,
}

impl std::ops::Index<hir::Fqn> for InferenceResult {
    type Output = Signature;

    fn index(&self, fqn: hir::Fqn) -> &Self::Output {
        &self.signatures[&fqn]
    }
}

impl std::ops::Index<hir::FileName> for InferenceResult {
    type Output = ModuleInference;

    fn index(&self, module: hir::FileName) -> &Self::Output {
        &self.modules[&module]
    }
}

impl std::ops::Index<Idx<hir::Expr>> for ModuleInference {
    type Output = Intern<ResolvedTy>;

    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        &self.expr_tys[expr]
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for ModuleInference {
    type Output = Intern<ResolvedTy>;

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

    pub fn into_function(self) -> Option<FunctionSignature> {
        match self {
            Signature::Function(signature) => Some(signature),
            Signature::Global(_) => None,
        }
    }

    pub fn into_global(self) -> Option<GlobalSignature> {
        match self {
            Signature::Function { .. } => None,
            Signature::Global(signature) => Some(signature),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub return_ty: Intern<ResolvedTy>,
    pub param_tys: Vec<Intern<ResolvedTy>>,
    pub is_extern: bool,
}

#[derive(Debug, Clone)]
pub struct GlobalSignature {
    pub ty: Intern<ResolvedTy>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TyDiagnostic {
    pub kind: TyDiagnosticKind,
    pub module: hir::FileName,
    pub range: TextRange,
    pub help: Option<TyDiagnosticHelp>,
}

impl TyDiagnostic {
    pub fn is_error(&self) -> bool {
        !matches!(self.kind, TyDiagnosticKind::IntTooBigForType { .. })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyDiagnosticKind {
    Mismatch {
        expected: Intern<ResolvedTy>,
        found: Intern<ResolvedTy>,
    },
    Uncastable {
        from: Intern<ResolvedTy>,
        to: Intern<ResolvedTy>,
    },
    BinaryOpMismatch {
        op: hir::BinaryOp,
        first: Intern<ResolvedTy>,
        second: Intern<ResolvedTy>,
    },
    UnaryOpMismatch {
        op: hir::UnaryOp,
        ty: Intern<ResolvedTy>,
    },
    IfMismatch {
        found: Intern<ResolvedTy>,
        expected: Intern<ResolvedTy>,
    },
    IndexNonArray {
        found: Intern<ResolvedTy>,
    },
    IndexOutOfBounds {
        index: u64,
        actual_size: u64,
        array_ty: Intern<ResolvedTy>,
    },
    MismatchedArgCount {
        found: usize,
        expected: usize,
    },
    CalledNonFunction {
        found: Intern<ResolvedTy>,
    },
    DerefNonPointer {
        found: Intern<ResolvedTy>,
    },
    DerefAny,
    MissingElse {
        expected: Intern<ResolvedTy>,
    },
    CannotMutate,
    MutableRefToImmutableData,
    NotYetResolved {
        path: hir::Path,
    },
    ParamNotATy,
    LocalTyIsMutable,
    IntTooBigForType {
        found: u64,
        max: u64,
        ty: Intern<ResolvedTy>,
    },
    UnknownModule {
        name: hir::FileName,
    },
    UnknownFqn {
        fqn: hir::Fqn,
    },
    NonExistentField {
        field: Key,
        found_ty: Intern<ResolvedTy>,
    },
    StructLiteralMissingField {
        field: Key,
        expected_ty: Intern<ResolvedTy>,
    },
    ComptimePointer,
    ComptimeType,
    GlobalNotConst,
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
    IfReturnsTypeHere { found: Intern<ResolvedTy> },
    MutableVariable,
}

pub struct InferenceCtx<'a> {
    current_module: Option<hir::FileName>,
    bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
    world_index: &'a hir::WorldIndex,
    twr_arena: &'a Arena<TyWithRange>,
    local_usages: FxHashMap<hir::FileName, ArenaMap<Idx<hir::LocalDef>, FxHashSet<LocalUsage>>>,
    param_tys: Option<Vec<Intern<ResolvedTy>>>,
    signatures: FxHashMap<hir::Fqn, Signature>,
    modules: FxHashMap<hir::FileName, ModuleInference>,
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
        bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
        world_index: &'a hir::WorldIndex,
        twr_arena: &'a Arena<TyWithRange>,
    ) -> InferenceCtx<'a> {
        Self {
            current_module: None,
            bodies_map,
            world_index,
            twr_arena,
            local_usages: FxHashMap::default(),
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
                    lambdas: ArenaMap::default(),
                },
            );
        }

        for (module, index) in self.world_index.get_all_modules() {
            for (name, global) in index.globals() {
                let fqn = hir::Fqn { module, name };

                #[allow(clippy::map_entry)]
                if !self.signatures.contains_key(&fqn) {
                    self.get_global_signature(global, fqn);
                }
            }

            for (name, function) in index.functions() {
                let fqn = hir::Fqn { module, name };

                #[allow(clippy::map_entry)]
                if !self.signatures.contains_key(&fqn) {
                    self.get_function_signature(function, fqn);
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
    fn get_global_signature(&mut self, global: &hir::Global, fqn: hir::Fqn) -> GlobalSignature {
        if let Some(sig) = self.signatures.get(&fqn) {
            return sig.as_global().unwrap().clone();
        }

        let old_module = self.current_module;
        self.current_module = Some(fqn.module);
        // if the global has a type annotation (my_global : string : "hello"),
        // we must treat it differently than one that does not (my_global :: "hello")
        let sig = match self.twr_arena[global.ty] {
            TyWithRange::Unknown => {
                self.signatures.insert(
                    fqn,
                    Signature::Global(GlobalSignature {
                        ty: Intern::new(ResolvedTy::NotYetResolved),
                    }),
                );

                let ty = self.finish_body_unknown(
                    self.bodies_map[&fqn.module].global(fqn.name),
                    None,
                    true,
                );

                Signature::Global(GlobalSignature { ty })
            }
            _ => {
                let sig = Signature::Global(GlobalSignature {
                    ty: self.resolve_ty(global.ty),
                });

                self.signatures.insert(fqn, sig.clone());

                self.finish_body_known(
                    self.bodies_map[&fqn.module].global(fqn.name),
                    None,
                    sig.as_global().unwrap().ty,
                    true,
                );

                sig
            }
        };

        self.signatures.insert(fqn, sig.clone());

        self.current_module = old_module;

        sig.into_global().unwrap()
    }

    /// could potentially return a non-function signature depending on the function's type annotation
    fn get_function_signature(&mut self, function: &hir::Function, fqn: hir::Fqn) -> Signature {
        if let Some(sig) = self.signatures.get(&fqn) {
            return sig.clone();
        }

        let old_module = self.current_module;
        self.current_module = Some(fqn.module);

        let param_tys: Vec<_> = function
            .params
            .iter()
            .map(|param| self.resolve_ty(param.ty))
            .collect();

        let return_ty = self.resolve_ty(function.return_ty);

        let ty_annotation = self.resolve_ty(function.ty_annotation);
        let sig = match ty_annotation.as_ref() {
            ResolvedTy::Unknown => {
                let sig = Signature::Function(FunctionSignature {
                    param_tys: param_tys.clone(),
                    return_ty,
                    is_extern: function.is_extern,
                });

                self.signatures.insert(fqn, sig.clone());

                if !function.is_extern {
                    self.finish_body_known(
                        self.bodies_map[&fqn.module].function_body(fqn.name),
                        Some(param_tys),
                        return_ty,
                        false,
                    );
                }

                sig
            }
            ResolvedTy::Function { .. } => {
                let found_ty = Intern::new(ResolvedTy::Function {
                    params: param_tys.clone(),
                    return_ty,
                });

                if found_ty != ty_annotation {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::Mismatch {
                            expected: ty_annotation,
                            found: found_ty,
                        },
                        module: self.current_module.unwrap(),
                        range: self.world_index.range_info(fqn).value,
                        help: None,
                    });
                }

                let (annotation_param_tys, annotation_return_ty) =
                    ty_annotation.as_function().unwrap();

                let annotation_sig = Signature::Function(FunctionSignature {
                    param_tys: annotation_param_tys,
                    return_ty: annotation_return_ty,
                    is_extern: function.is_extern,
                });

                self.signatures.insert(fqn, annotation_sig.clone());

                if !function.is_extern {
                    self.finish_body_known(
                        self.bodies_map[&fqn.module].function_body(fqn.name),
                        Some(param_tys),
                        return_ty,
                        false,
                    );
                }

                annotation_sig
            }
            _ => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::Mismatch {
                        expected: ty_annotation,
                        found: Intern::new(ResolvedTy::Function {
                            params: param_tys.clone(),
                            return_ty,
                        }),
                    },
                    module: self.current_module.unwrap(),
                    range: self.world_index.range_info(fqn).value,
                    help: None,
                });

                let annotation_sig = Signature::Global(GlobalSignature { ty: ty_annotation });

                self.signatures.insert(fqn, annotation_sig.clone());

                if !function.is_extern {
                    self.finish_body_known(
                        self.bodies_map[&fqn.module].function_body(fqn.name),
                        Some(param_tys),
                        return_ty,
                        false,
                    );
                }

                annotation_sig
            }
        };

        self.current_module = old_module;

        sig
    }

    /// newly constructs the signature of a function, possibly throwing diagnostics.
    /// please use `singleton_fn_signature` instead
    fn generate_lambda_signature(&mut self, lambda: Idx<hir::Lambda>) -> FunctionSignature {
        let hir::Lambda { function, body } =
            &self.bodies_map[&self.current_module.unwrap()][lambda];

        let return_ty = self.resolve_ty(function.return_ty);

        let param_tys: Vec<_> = function
            .params
            .iter()
            .map(|param| self.resolve_ty(param.ty))
            .collect();

        let sig = FunctionSignature {
            param_tys,
            return_ty,
            is_extern: function.is_extern,
        };

        self.modules
            .get_mut(&self.current_module.unwrap())
            .unwrap()
            .lambdas
            .insert(lambda, sig.clone());

        if !function.is_extern {
            self.finish_body_known(*body, Some(sig.param_tys.clone()), sig.return_ty, false);
        }

        sig
    }

    fn path_with_range_to_ty(&mut self, path: hir::PathWithRange) -> Intern<ResolvedTy> {
        let (fqn, module_range, name_range) = match path {
            hir::PathWithRange::ThisModule(NameWithRange { name, range }) => (
                hir::Fqn {
                    module: self.current_module.unwrap(),
                    name,
                },
                None,
                range,
            ),
            hir::PathWithRange::OtherModule {
                fqn,
                module_range,
                name_range,
            } => (fqn, Some(module_range), name_range),
        };

        match self.world_index.get_definition(fqn) {
            Ok(definition) => match definition {
                hir::Definition::Global(global) => {
                    let global_ty = self.get_global_signature(global, fqn).ty;

                    if *global_ty == ResolvedTy::Unknown {
                        return ResolvedTy::Unknown.into();
                    }

                    if *global_ty != ResolvedTy::Type {
                        if !global_ty.is_unknown() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Mismatch {
                                    expected: ResolvedTy::Type.into(),
                                    found: global_ty,
                                },
                                module: self.current_module.unwrap(),
                                range: name_range,
                                help: None,
                            });
                        }
                        return ResolvedTy::Unknown.into();
                    }

                    let global_body = self.bodies_map[&fqn.module].global(fqn.name);

                    let old_module = self.current_module.replace(fqn.module);

                    let actual_ty = self.parse_expr_to_ty(global_body);

                    self.current_module = old_module;

                    // todo: here the intern ptr changes, even though the type is really still the same
                    match actual_ty.as_ref() {
                        ResolvedTy::Distinct {
                            fqn: None,
                            uid,
                            ty: distinct_ty,
                        } => ResolvedTy::Distinct {
                            fqn: Some(fqn),
                            uid: *uid,
                            ty: *distinct_ty,
                        }
                        .into(),
                        ResolvedTy::Struct { fqn: None, fields } => ResolvedTy::Struct {
                            fqn: Some(fqn),
                            fields: fields.clone(),
                        }
                        .into(),
                        _ => actual_ty,
                    }
                }
                hir::Definition::Function(func) => {
                    let global_ty = self.get_function_signature(func, fqn);

                    match global_ty {
                        Signature::Function(func) => {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Mismatch {
                                    expected: ResolvedTy::Type.into(),
                                    found: ResolvedTy::Function {
                                        params: func.param_tys,
                                        return_ty: func.return_ty,
                                    }
                                    .into(),
                                },
                                module: self.current_module.unwrap(),
                                range: name_range,
                                help: None,
                            });

                            ResolvedTy::Unknown.into()
                        }
                        Signature::Global(_) => ResolvedTy::Unknown.into(),
                    }
                }
            },
            Err(hir::GetDefinitionError::UnknownModule) => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownModule { name: fqn.module },
                    module: self.current_module.unwrap(),
                    range: module_range.unwrap(),
                    help: None,
                });
                ResolvedTy::Unknown.into()
            }
            Err(hir::GetDefinitionError::UnknownDefinition) => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFqn { fqn },
                    module: self.current_module.unwrap(),
                    range: name_range,
                    help: None,
                });
                ResolvedTy::Unknown.into()
            }
        }
    }

    fn parse_expr_to_ty(&mut self, expr: Idx<hir::Expr>) -> Intern<ResolvedTy> {
        match &self.bodies_map[&self.current_module.unwrap()][expr] {
            hir::Expr::Missing => ResolvedTy::Unknown.into(),
            hir::Expr::Ref { mutable, expr } => {
                let sub_ty = self.parse_expr_to_ty(*expr);

                ResolvedTy::Pointer {
                    mutable: *mutable,
                    sub_ty,
                }
                .into()
            }
            hir::Expr::Local(local_def) => {
                let local_ty = self.modules[&self.current_module.unwrap()].local_tys[*local_def];

                if *local_ty == ResolvedTy::Unknown {
                    return ResolvedTy::Unknown.into();
                }

                if *local_ty != ResolvedTy::Type {
                    if !local_ty.is_unknown() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::Mismatch {
                                expected: ResolvedTy::Type.into(),
                                found: self.modules[&self.current_module.unwrap()].local_tys
                                    [*local_def],
                            },
                            module: self.current_module.unwrap(),
                            range: self.bodies_map[&self.current_module.unwrap()]
                                .range_for_expr(expr),
                            help: None,
                        });
                    }

                    return ResolvedTy::Unknown.into();
                }

                let local_def = &self.bodies_map[&self.current_module.unwrap()][*local_def];

                if local_def.mutable {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::LocalTyIsMutable,
                        module: self.current_module.unwrap(),
                        range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                        help: Some(TyDiagnosticHelp {
                            kind: TyDiagnosticHelpKind::MutableVariable,
                            range: local_def.range,
                        }),
                    });

                    return ResolvedTy::Unknown.into();
                }

                self.parse_expr_to_ty(local_def.value)
            }
            hir::Expr::SelfGlobal(name) => {
                self.path_with_range_to_ty(hir::PathWithRange::ThisModule(*name))
            }
            hir::Expr::Param { .. } => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::ParamNotATy,
                    module: self.current_module.unwrap(),
                    range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                    help: None,
                });

                ResolvedTy::Unknown.into()
            }
            hir::Expr::Path { previous, field } => {
                let previous_ty = self.infer_expr(*previous);
                match previous_ty.as_ref() {
                    ResolvedTy::Module(module) => {
                        let path = hir::PathWithRange::OtherModule {
                            fqn: hir::Fqn {
                                module: *module,
                                name: field.name,
                            },
                            module_range: self.bodies_map[&self.current_module.unwrap()]
                                .range_for_expr(*previous),
                            name_range: field.range,
                        };

                        self.path_with_range_to_ty(path)
                    }
                    _ => {
                        let expr_ty = self.infer_expr(expr);
                        if !expr_ty.is_unknown() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Mismatch {
                                    expected: ResolvedTy::Type.into(),
                                    found: expr_ty,
                                },
                                module: self.current_module.unwrap(),
                                range: self.bodies_map[&self.current_module.unwrap()]
                                    .range_for_expr(expr),
                                help: None,
                            });
                        }

                        ResolvedTy::Unknown.into()
                    }
                }
            }
            hir::Expr::PrimitiveTy { ty } => self.resolve_ty(*ty),
            _ => {
                let expr_ty = self.infer_expr(expr);
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::Type.into(),
                        found: expr_ty,
                    },
                    module: self.current_module.unwrap(),
                    range: self.bodies_map[&self.current_module.unwrap()].range_for_expr(expr),
                    help: None,
                });

                ResolvedTy::Unknown.into()
            }
        }
    }

    fn resolve_ty(&mut self, ty: Idx<hir::TyWithRange>) -> Intern<ResolvedTy> {
        match self.twr_arena[ty].clone() {
            hir::TyWithRange::Unknown => ResolvedTy::Unknown.into(),
            hir::TyWithRange::IInt { bit_width, .. } => ResolvedTy::IInt(bit_width).into(),
            hir::TyWithRange::UInt { bit_width, .. } => ResolvedTy::UInt(bit_width).into(),
            hir::TyWithRange::Float { bit_width, .. } => ResolvedTy::Float(bit_width).into(),
            hir::TyWithRange::Bool { .. } => ResolvedTy::Bool.into(),
            hir::TyWithRange::String { .. } => ResolvedTy::String.into(),
            hir::TyWithRange::Array { size, sub_ty, .. } => ResolvedTy::Array {
                size,
                sub_ty: self.resolve_ty(sub_ty),
            }
            .into(),
            hir::TyWithRange::Pointer {
                mutable, sub_ty, ..
            } => ResolvedTy::Pointer {
                mutable,
                sub_ty: self.resolve_ty(sub_ty),
            }
            .into(),
            hir::TyWithRange::Distinct { uid, ty, .. } => ResolvedTy::Distinct {
                fqn: None,
                uid,
                ty: self.resolve_ty(ty),
            }
            .into(),
            hir::TyWithRange::Type { .. } => ResolvedTy::Type.into(),
            hir::TyWithRange::Any { .. } => ResolvedTy::Any.into(),
            hir::TyWithRange::Named { path } => self.path_with_range_to_ty(path),
            hir::TyWithRange::Void { .. } => ResolvedTy::Void.into(),
            hir::TyWithRange::Function {
                params, return_ty, ..
            } => ResolvedTy::Function {
                params: params
                    .into_iter()
                    .map(|param| self.resolve_ty(param))
                    .collect(),
                return_ty: self.resolve_ty(return_ty),
            }
            .into(),
            hir::TyWithRange::Struct { fields, .. } => ResolvedTy::Struct {
                fqn: None,
                fields: fields
                    .iter()
                    .cloned()
                    .filter_map(|(name, ty)| name.map(|name| (name, self.resolve_ty(ty))))
                    .collect(),
            }
            .into(),
        }
    }
}

impl InferenceResult {
    fn shrink_to_fit(&mut self) {
        let Self {
            signatures,
            modules,
        } = self;
        signatures.shrink_to_fit();
        modules.shrink_to_fit();
    }
}

impl InferenceResult {
    pub fn debug(
        &self,
        project_root: &std::path::Path,
        interner: &Interner,
        fancy: bool,
    ) -> String {
        let mut s = String::new();

        let mut signatures = self
            .signatures
            .iter()
            .map(|(fqn, sig)| (fqn.to_string(project_root, interner), sig))
            .collect::<Vec<_>>();

        signatures.sort_by(|(fqn1, _), (fqn2, _)| fqn1.cmp(fqn2));

        for (fqn, signature) in signatures {
            match signature {
                Signature::Function(FunctionSignature {
                    return_ty,
                    param_tys,
                    is_extern,
                }) => {
                    s.push_str(&fqn);
                    s.push_str(" : ");

                    if *is_extern {
                        s.push_str("extern ");
                    }
                    s.push('(');
                    for (idx, param_ty) in param_tys.iter().enumerate() {
                        if idx != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&param_ty.display(project_root, interner));
                    }
                    s.push(')');

                    s.push_str(&format!(
                        " -> {}\n",
                        return_ty.display(project_root, interner)
                    ));
                }
                Signature::Global(GlobalSignature { ty }) => {
                    s.push_str(&fqn);
                    s.push_str(" : ");
                    s.push_str(&format!("{}\n", ty.display(project_root, interner)));
                }
            }
        }

        let mut modules = self.modules.iter().collect::<Vec<_>>();
        modules.sort_by_key(|(name, _)| **name);

        for (name, module) in modules {
            if fancy || self.modules.len() > 1 {
                s.push_str(&format!("{}:\n", name.to_string(project_root, interner)));
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
                s.push_str(&format!(" : {}\n", ty.display(project_root, interner)));
            }

            for (local_def_idx, ty) in module.local_tys.iter() {
                if fancy || self.modules.len() > 1 {
                    s.push_str("  ");
                }
                s.push_str(&format!(
                    "l{} : {}\n",
                    local_def_idx.into_raw(),
                    ty.display(project_root, interner)
                ));
            }
        }

        s
    }
}

impl ResolvedTy {
    pub fn display(&self, project_root: &std::path::Path, interner: &Interner) -> String {
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
                format!("[{size}]{}", sub_ty.display(project_root, interner))
            }
            Self::Pointer { mutable, sub_ty } => {
                format!(
                    "^{}{}",
                    if *mutable { "mut " } else { "" },
                    sub_ty.display(project_root, interner)
                )
            }
            Self::Distinct { fqn: Some(fqn), .. } => fqn.to_string(project_root, interner),
            Self::Distinct { fqn: None, uid, ty } => {
                format!("distinct'{} {}", uid, ty.display(project_root, interner))
            }
            Self::Function { params, return_ty } => {
                let mut res = "(".to_string();

                for (idx, param) in params.iter().enumerate() {
                    res.push_str(&param.display(project_root, interner));

                    if idx != params.len() - 1 {
                        res.push_str(", ");
                    }
                }
                res.push_str(") -> ");
                res.push_str(&return_ty.display(project_root, interner));

                res
            }
            Self::Struct { fqn: Some(fqn), .. } => fqn.to_string(project_root, interner),
            Self::Struct { fqn: None, fields } => {
                let mut res = "struct {".to_string();

                for (idx, (name, ty)) in fields.iter().enumerate() {
                    res.push_str(interner.lookup(name.0));
                    res.push_str(": ");

                    res.push_str(&ty.display(project_root, interner));

                    if idx != fields.len() - 1 {
                        res.push_str(", ");
                    }
                }

                res.push('}');

                res
            }
            Self::Type => "type".to_string(),
            Self::Any => "any".to_string(),
            Self::Void => "void".to_string(),
            Self::Module(file_name) => {
                format!("module {}", file_name.to_string(project_root, interner))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{path::Path, vec};

    use super::*;
    use ast::AstNode;
    use expect_test::{expect, Expect};
    use interner::Interner;
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
        let modules = test_utils::split_multi_module_test_data(input);
        let mut interner = Interner::default();
        let mut world_index = hir::WorldIndex::default();

        let mut uid_gen = UIDGenerator::default();
        let mut twr_arena = Arena::new();
        let mut bodies_map = FxHashMap::default();

        for (name, text) in &modules {
            if *name == "main.capy" {
                continue;
            }

            let tokens = lexer::lex(text);
            let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
            let root = ast::Root::cast(tree.root(), &tree).unwrap();
            let (index, _) = hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

            let module = hir::FileName(interner.intern(name));

            let (bodies, _) = hir::lower(
                root,
                &tree,
                Path::new(name),
                &index,
                &mut uid_gen,
                &mut twr_arena,
                &mut interner,
                true,
            );
            world_index.add_module(module, index);
            bodies_map.insert(module, bodies);
        }

        let text = &modules["main.capy"];
        let module = hir::FileName(interner.intern("main.capy"));
        let tokens = lexer::lex(text);
        let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut uid_gen, &mut twr_arena, &mut interner);

        let (bodies, _) = hir::lower(
            root,
            &tree,
            Path::new("main"),
            &index,
            &mut uid_gen,
            &mut twr_arena,
            &mut interner,
            true,
        );
        world_index.add_module(module, index);
        bodies_map.insert(module, bodies);

        let (inference_result, actual_diagnostics) =
            InferenceCtx::new(&bodies_map, &world_index, &twr_arena).finish();

        expect.assert_eq(&inference_result.debug(Path::new(""), &interner, false));

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
                foo :: () {};
            "#,
            expect![[r#"
                main::foo : () -> void
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
                main::one : () -> i32
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
                main::one : () -> f32
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
                main::one : () -> f32
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
                main::one : () -> <unknown>
                main::two : () -> <unknown>
                0 : void
                1 : void
            "#]],
            |i| {
                [
                    (
                        TyDiagnosticKind::UnknownFqn {
                            fqn: hir::Fqn {
                                module: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("foo")),
                            },
                        },
                        30..33,
                        None,
                    ),
                    // (
                    //     TyDiagnosticKind::UnknownModule {
                    //         name: hir::FileName { key: i.intern("bar")),
                    //     },
                    //     67..70,
                    //     None,
                    // ),
                ]
            },
        );
    }

    #[test]
    fn ty_in_other_module() {
        check(
            r#"
                #- main.capy
                numbers :: import "numbers.capy";

                // todo: allow functions to return types defined in other modules w/o having to do this
                imaginary :: numbers.imaginary;

                fun :: () -> imaginary {
                    foo : numbers.imaginary = 0;

                    my_magic := numbers.Magic_Struct {
                        mystical_field: 123 as numbers.imaginary,
                    }

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
                main::imaginary : type
                main::numbers : module numbers
                numbers::Magic_Struct : type
                numbers::imaginary : type
                numbers:
                  0 : type
                  1 : type
                main:
                  0 : module numbers
                  1 : module numbers
                  2 : type
                  3 : module numbers
                  5 : numbers::imaginary
                  7 : module numbers
                  9 : numbers::imaginary
                  10 : module numbers
                  12 : numbers::imaginary
                  13 : numbers::Magic_Struct
                  14 : numbers::Magic_Struct
                  15 : numbers::imaginary
                  16 : numbers::imaginary
                  l0 : numbers::imaginary
                  l1 : numbers::Magic_Struct
            "#]],
            |_| [],
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
                main::calc : () -> isize
                1 : i128
                3 : i128
                5 : u16
                7 : u16
                8 : i128
                9 : u16
                10 : i128
                11 : i128
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
                main::calc : () -> u128
                1 : u16
                3 : u16
                4 : u16
                5 : u16
                6 : u16
                7 : u16
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
                1 : u16
                2 : u16
                3 : i128
                4 : i128
                5 : i128
                6 : i128
                l0 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::UInt(16).into(),
                        second: ResolvedTy::IInt(0).into(),
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
                main::check : () -> bool
                1 : {uint}
                3 : {uint}
                5 : bool
                6 : bool
                7 : bool
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
                main::how_old : () -> usize
                1 : string
                3 : string
                5 : usize
                6 : usize
                7 : usize
                l0 : string
                l1 : usize
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: ResolvedTy::String.into(),
                        to: ResolvedTy::UInt(u32::MAX).into(),
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
                1 : usize
                3 : usize
                5 : usize
                6 : void
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
                    my_array := [] i32 { 4, 8, 15, 16, 23, 42 };
                };
            "#,
            expect![[r#"
                main::main : () -> void
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : [6]i32
                9 : void
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_with_size() {
        check(
            r#"
                main :: () {
                    my_array := [6] i32 { 4, 8, 15, 16, 23, 42 };
                };
            "#,
            expect![[r#"
                main::main : () -> void
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : [6]i32
                9 : void
                l0 : [6]i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_with_incorrect_size() {
        check(
            r#"
                main :: () {
                    my_array := [7] i32 { 4, 8, 15, 16, 23, 42 };
                };
            "#,
            expect![[r#"
                main::main : () -> void
                2 : i32
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : [7]i32
                9 : void
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
                l0 : [6]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexOutOfBounds {
                        index: 1000,
                        actual_size: 6,
                        array_ty: ResolvedTy::Array {
                            size: 6,
                            sub_ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
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
                2 : i16
                3 : bool
                4 : i16
                5 : i16
                6 : i16
                7 : i16
                8 : i16
                9 : i16
                10 : i16
                11 : void
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
                3 : usize
                4 : usize
                5 : usize
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
                2 : i8
                3 : bool
                4 : i8
                5 : i8
                6 : i8
                7 : i8
                8 : i8
                9 : i8
                10 : i8
                11 : i8
                12 : i8
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
                2 : u8
                3 : bool
                4 : u8
                5 : u8
                6 : u8
                7 : u8
                8 : u8
                9 : u8
                10 : u8
                11 : u8
                12 : u8
                l0 : u8
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8).into(),
                        found: ResolvedTy::IInt(0).into(),
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
                main::add : (i32, i32) -> i32
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
                main :: () {
                    a := 10;
                    a;
                };
            "#,
            expect![[r#"
                main::main : () -> void
                1 : {uint}
                2 : {uint}
                3 : void
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
                1 : {uint}
                3 : string
                4 : string
                5 : void
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
                foo :: () {
                    a := "Hello";
                    a = "World"; // `a` on the left is an expression, and it's type is evaluated
                    a;
                };
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : string
                2 : string
                3 : string
                4 : string
                5 : void
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
                main::foo : () -> i16
                1 : i8
                3 : i8
                4 : i16
                5 : i16
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
                1 : u16
                3 : u16
                4 : u8
                5 : u8
                l0 : u16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8).into(),
                        found: ResolvedTy::UInt(16).into(),
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
                1 : u8
                3 : u8
                4 : i16
                5 : i16
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
                1 : i8
                3 : i8
                4 : u16
                5 : u16
                l0 : i8
                l1 : u16
            "#]],
            |_| {
                // should fail due to loss of sign
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(16).into(),
                        found: ResolvedTy::IInt(8).into(),
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
                1 : i16
                3 : i16
                4 : u16
                5 : u16
                l0 : i16
                l1 : u16
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(16).into(),
                        found: ResolvedTy::IInt(16).into(),
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
                1 : i16
                3 : i16
                4 : u8
                5 : u8
                l0 : i16
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8).into(),
                        found: ResolvedTy::IInt(16).into(),
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
                0 : string
                1 : i32
                2 : i32
                3 : i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::String.into(),
                        second: ResolvedTy::UInt(0).into(),
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
                main::f : () -> string
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
                main::f : () -> bool
                0 : bool
                1 : {uint}
                2 : bool
                3 : bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Lt,
                        first: ResolvedTy::Bool.into(),
                        second: ResolvedTy::UInt(0).into(),
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
                0 : string
                1 : string
                2 : bool
                3 : bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::And,
                        first: ResolvedTy::String.into(),
                        second: ResolvedTy::String.into(),
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
                main::either : () -> bool
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
                main::less : () -> bool
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
                main::equality : () -> bool
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
                main::redundant : () -> u8
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
                main::neg : () -> u8
                0 : u8
                1 : u8
                2 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::UInt(8).into(),
                        found: ResolvedTy::IInt(0).into(),
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
                main::pos : () -> i8
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
                main::not : () -> bool
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
                main::s : () -> string
                0 : {uint}
                1 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::String.into(),
                        found: ResolvedTy::UInt(0).into(),
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
                main :: () { nothing(); };
                nothing :: () {};
            "#,
            expect![[r#"
                main::main : () -> void
                main::nothing : () -> void
                0 : () -> void
                1 : void
                2 : void
                3 : void
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
                0 : () -> i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
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
                0 : (i32) -> i32
                1 : i32
                2 : i32
                3 : i32
                4 : i32
                5 : i32
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
                0 : (i32, i32) -> i32
                1 : void
                2 : string
                3 : i32
                4 : i32
                5 : i32
                6 : i32
                7 : i32
                8 : i32
            "#]],
            |_| {
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::IInt(32).into(),
                            found: ResolvedTy::Void.into(),
                        },
                        46..48,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::IInt(32).into(),
                            found: ResolvedTy::String.into(),
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
                #- main.capy
                a :: () -> string {
                    greetings := import "greetings.capy"

                    greetings.informal(10)
                };
                #- greetings.capy
                informal :: (n: i32) -> string { "Hello!" };
            "#,
            expect![[r#"
                greetings::informal : (i32) -> string
                main::a : () -> string
                greetings:
                  0 : string
                  1 : string
                main:
                  1 : module greetings
                  2 : module greetings
                  3 : (i32) -> string
                  4 : i32
                  5 : string
                  6 : string
                  l0 : module greetings
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
                2 : {uint}
                3 : {uint}
                4 : {uint}
                5 : string
                6 : string
                7 : void
                8 : void
                9 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::IInt(32).into(),
                        found: ResolvedTy::String.into(),
                    },
                    123..128,
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
                main::imaginary : type
                main::main : () -> i32
                0 : type
                2 : main::imaginary
                3 : main::imaginary
                4 : main::imaginary
                l0 : main::imaginary
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::IInt(32).into(),
                        found: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
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
                main::imaginary : type
                main::main : () -> main::imaginary
                0 : type
                2 : main::imaginary
                3 : main::imaginary
                4 : main::imaginary
                5 : main::imaginary
                6 : main::imaginary
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
                0 : type
                2 : main::imaginary
                3 : main::imaginary
                4 : main::imaginary
                5 : main::imaginary
                6 : main::imaginary
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
                0 : type
                2 : main::imaginary
                4 : i32
                5 : main::imaginary
                6 : i32
                7 : main::imaginary
                8 : main::imaginary
                l0 : main::imaginary
                l1 : i32
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
                        second: ResolvedTy::IInt(32).into(),
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
                0 : type
                1 : type
                3 : main::imaginary
                5 : main::extra_imaginary
                6 : main::imaginary
                7 : main::extra_imaginary
                8 : main::imaginary
                9 : main::imaginary
                l0 : main::imaginary
                l1 : main::extra_imaginary
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::BinaryOpMismatch {
                        op: hir::BinaryOp::Add,
                        first: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
                        second: ResolvedTy::Distinct {
                            fqn: Some(hir::Fqn {
                                module: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("extra_imaginary")),
                            }),
                            uid: 1,
                            ty: ResolvedTy::IInt(32).into(),
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

                    {i as ^i32}^
                };
            "#,
            expect![[r#"
                main::main : () -> i32
                main::something_far_away : type
                0 : type
                2 : i32
                3 : main::something_far_away
                4 : main::something_far_away
                6 : ^i32
                7 : ^i32
                8 : i32
                9 : i32
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

                    {x as ^imaginary}^
                };
            "#,
            expect![[r#"
                main::imaginary : type
                main::imaginary_far_away : type
                main::main : () -> main::imaginary
                0 : type
                1 : type
                3 : main::imaginary
                5 : main::imaginary
                6 : main::imaginary_far_away
                7 : main::imaginary_far_away
                10 : ^main::imaginary
                11 : ^main::imaginary
                12 : main::imaginary
                13 : main::imaginary
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
                    my_point : Vector3 = [] i32 { 4, 8, 15 };

                    x := my_point[0];
                    y := my_point[1];
                    z := my_point[2];
                };
            "#,
            expect![[r#"
                main::Vector3 : type
                main::main : () -> void
                0 : type
                3 : i32
                4 : i32
                5 : i32
                6 : [3]i32
                8 : main::Vector3
                9 : usize
                10 : i32
                12 : main::Vector3
                13 : usize
                14 : i32
                16 : main::Vector3
                17 : usize
                18 : i32
                19 : void
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
                1 : i32
                2 : i32
                3 : ^i32
                4 : ^i32
                l0 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn recursive_definition() {
        check(
            r#"
                foo :: comptime { bar };

                bar :: comptime { foo };
            "#,
            expect![[r#"
                main::bar : <unknown>
                main::foo : <unknown>
                0 : <unknown>
                1 : <unknown>
                2 : <unknown>
                3 : <unknown>
                4 : <unknown>
                5 : <unknown>
            "#]],
            |interner| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        path: hir::Path::ThisModule(hir::Name(interner.intern("foo"))),
                    },
                    77..80,
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
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : void
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
                1 : {uint}
                2 : {uint}
                3 : {uint}
                4 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    81..89,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 50..58)),
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
                1 : {uint}
                3 : {uint}
                4 : ^{uint}
                5 : ^{uint}
                6 : {uint}
                7 : {uint}
                8 : void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    115..124,
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
                1 : {uint}
                3 : {uint}
                4 : ^mut {uint}
                5 : ^mut {uint}
                6 : {uint}
                7 : {uint}
                8 : void
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
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    50..59,
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
                1 : {uint}
                3 : {uint}
                4 : ^mut {uint}
                5 : void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    87..95,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 50..58)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_struct_field() {
        check(
            r#"
                Person :: struct {
                    name: string,
                    age: i32
                };

                foo :: () {
                    bob := Person {
                        name: "Bob",
                        age: 26,
                    };

                    bob.age = bob.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                0 : type
                3 : string
                4 : i32
                5 : main::Person
                6 : main::Person
                7 : i32
                8 : main::Person
                9 : i32
                10 : i32
                11 : i32
                12 : void
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
                    name: string,
                    age: i32
                };

                foo :: () {
                    bob :: Person {
                        name: "Bob",
                        age: 26,
                    };

                    bob.age = bob.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                0 : type
                3 : string
                4 : i32
                5 : main::Person
                6 : main::Person
                7 : i32
                8 : main::Person
                9 : i32
                10 : i32
                11 : i32
                12 : void
                l0 : main::Person
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    297..318,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 167..274)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_struct_array_field() {
        check(
            r#"
                Person :: struct {
                    name: string,
                    age: i32
                };

                Company :: struct {
                    employees: [3]Person,
                };

                foo :: () {
                    my_company := Company {
                        employees: [] Person {
                            Person {
                                name: "Bob",
                                age: 26,
                            },
                            Person {
                                name: "Kyle",
                                age: 30,
                            },
                            Person {
                                name: "John",
                                age: 23,
                            }
                        },
                    };

                    my_company.employees[1].age = my_company.employees[1].age + 1;
                }
            "#,
            expect![[r#"
                main::Company : type
                main::Person : type
                main::foo : () -> void
                0 : type
                1 : type
                6 : string
                7 : i32
                8 : main::Person
                10 : string
                11 : i32
                12 : main::Person
                14 : string
                15 : i32
                16 : main::Person
                17 : [3]main::Person
                18 : main::Company
                19 : main::Company
                20 : [3]main::Person
                21 : usize
                22 : main::Person
                23 : i32
                24 : main::Company
                25 : [3]main::Person
                26 : usize
                27 : main::Person
                28 : i32
                29 : i32
                30 : i32
                31 : void
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
                    name: string,
                    age: i32
                };

                Company :: struct {
                    employees: [3]Person,
                };

                foo :: () {
                    my_company :: Company {
                        employees: [] Person {
                            Person {
                                name: "Bob",
                                age: 26,
                            },
                            Person {
                                name: "Kyle",
                                age: 30,
                            },
                            Person {
                                name: "John",
                                age: 23,
                            }
                        },
                    };

                    my_company.employees[1].age = my_company.employees[1].age + 1;
                }
            "#,
            expect![[r#"
                main::Company : type
                main::Person : type
                main::foo : () -> void
                0 : type
                1 : type
                6 : string
                7 : i32
                8 : main::Person
                10 : string
                11 : i32
                12 : main::Person
                14 : string
                15 : i32
                16 : main::Person
                17 : [3]main::Person
                18 : main::Company
                19 : main::Company
                20 : [3]main::Person
                21 : usize
                22 : main::Person
                23 : i32
                24 : main::Company
                25 : [3]main::Person
                26 : usize
                27 : main::Person
                28 : i32
                29 : i32
                30 : i32
                31 : void
                l0 : main::Company
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    870..931,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 265..847)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_struct_immutable_ref_field() {
        check(
            r#"
                Person :: struct {
                    name: string,
                    age: i32
                };

                Ref_To_Person :: struct {
                    person: ^Person,
                };

                foo :: () {
                    ref :: Ref_To_Person {
                        person: ^Person {
                            name: "Bob",
                            age: 26,
                        },
                    };

                    ref.person^.age = ref.person^.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::Ref_To_Person : type
                main::foo : () -> void
                0 : type
                1 : type
                5 : string
                6 : i32
                7 : main::Person
                8 : ^main::Person
                9 : main::Ref_To_Person
                10 : main::Ref_To_Person
                11 : ^main::Person
                12 : main::Person
                13 : i32
                14 : main::Ref_To_Person
                15 : ^main::Person
                16 : main::Person
                17 : i32
                18 : i32
                19 : i32
                20 : void
                l0 : main::Ref_To_Person
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    480..517,
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
                    name: string,
                    age: i32
                };

                Ref_To_Person :: struct {
                    person: ^mut Person,
                };

                foo :: () {
                    ref :: Ref_To_Person {
                        person: ^mut Person {
                            name: "Bob",
                            age: 26,
                        },
                    };

                    ref.person^.age = ref.person^.age + 1;
                }
            "#,
            expect![[r#"
                main::Person : type
                main::Ref_To_Person : type
                main::foo : () -> void
                0 : type
                1 : type
                5 : string
                6 : i32
                7 : main::Person
                8 : ^mut main::Person
                9 : main::Ref_To_Person
                10 : main::Ref_To_Person
                11 : ^mut main::Person
                12 : main::Person
                13 : i32
                14 : main::Ref_To_Person
                15 : ^mut main::Person
                16 : main::Person
                17 : i32
                18 : i32
                19 : i32
                20 : void
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
                    array := []i32 { 1, 2, 3 };

                    array[0] = 100;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : i32
                3 : i32
                4 : i32
                5 : [3]i32
                6 : [3]i32
                7 : usize
                8 : i32
                9 : i32
                10 : void
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
                    array :: []i32 { 1, 2, 3 };

                    array[0] = 100;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : i32
                3 : i32
                4 : i32
                5 : [3]i32
                6 : [3]i32
                7 : usize
                8 : i32
                9 : {uint}
                10 : void
                l0 : [3]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    98..112,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 49..75)),
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
                0 : i32
                1 : {uint}
                2 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    55..60,
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
                0 : ^i32
                1 : ^^i32
                2 : void
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
                0 : ^i32
                1 : ^mut ^i32
                2 : void
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
                0 : ^mut i32
                1 : ^mut ^mut i32
                2 : void
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
                0 : [3]i32
                1 : usize
                2 : i32
                3 : {uint}
                4 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    62..74,
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
                0 : ^i32
                1 : i32
                2 : {uint}
                3 : void
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
    fn assign_to_param_mut_ref() {
        check(
            r#"
                foo :: (array: ^mut i32) {
                    array^ = 5;
                }
            "#,
            expect![[r#"
                main::foo : (^mut i32) -> void
                0 : ^mut i32
                1 : i32
                2 : i32
                3 : void
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
                0 : ^i32
                1 : {uint}
                2 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    59..67,
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
                0 : ^mut i32
                1 : {uint}
                2 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    63..71,
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
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    76..83,
                    Some((TyDiagnosticHelpKind::ImmutableGlobal, 17..25)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_global_in_other_module() {
        check(
            r#"
                #- main.capy
                other_file :: import "other_file.capy";

                func :: () {
                    other_file.foo = 25;
                }
                #- other_file.capy
                foo :: 5;
            "#,
            expect![[r#"
                main::func : () -> void
                main::other_file : module other_file
                other_file::foo : i32
                other_file:
                  0 : i32
                main:
                  0 : module other_file
                  1 : module other_file
                  2 : i32
                  3 : {uint}
                  4 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    106..125,
                    Some((TyDiagnosticHelpKind::ImmutableGlobal, 117..120)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_immutable_ref_no_deref() {
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
                1 : {uint}
                3 : {uint}
                4 : ^{uint}
                5 : ^{uint}
                6 : {uint}
                7 : void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    114..122,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 87..91)),
                )]
            },
        );
    }

    #[test]
    fn assign_to_mut_ref_no_deref() {
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
                1 : {uint}
                3 : {uint}
                4 : ^mut {uint}
                5 : ^mut {uint}
                6 : {uint}
                7 : void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    118..126,
                    Some((TyDiagnosticHelpKind::NotMutatingRefThroughDeref, 118..121)),
                )]
            },
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
                1 : {uint}
                3 : {uint}
                4 : ^{uint}
                5 : ^{uint}
                6 : ^mut ^{uint}
                7 : void
                l0 : {uint}
                l1 : ^{uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    114..122,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 80..91)),
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
                1 : {uint}
                3 : {uint}
                4 : ^mut {uint}
                5 : ^mut {uint}
                6 : ^mut ^mut {uint}
                7 : void
                l0 : {uint}
                l1 : ^mut {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MutableRefToImmutableData,
                    118..126,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 80..95)),
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
                1 : usize
                3 : usize
                4 : usize
                5 : usize
                6 : usize
                7 : usize
                8 : (usize) -> void
                9 : usize
                10 : void
                11 : void
                12 : void
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
                1 : i32
                2 : (^i32) -> void
                3 : i32
                4 : ^i32
                5 : void
                6 : void
                7 : void
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
                1 : {uint}
                2 : (^mut i32) -> void
                3 : {uint}
                4 : ^{uint}
                5 : void
                6 : void
                7 : void
                l0 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::Pointer {
                            mutable: true,
                            sub_ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
                        found: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: ResolvedTy::UInt(0).into(),
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
                0 : void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn fn_with_diff_fn_annotation() {
        check(
            r#"
                foo : (arg: f32, arg2: i8) -> string : (x: i32) {
                    foo(x);
                };
            "#,
            expect![[r#"
                main::foo : (f32, i8) -> string
                0 : (f32, i8) -> string
                1 : i32
                2 : string
                3 : void
            "#]],
            |_| {
                let float = ResolvedTy::Float(32).into();
                let int = ResolvedTy::IInt(32).into();
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::Function {
                                params: vec![float, ResolvedTy::IInt(8).into()],
                                return_ty: ResolvedTy::String.into(),
                            }
                            .into(),
                            found: ResolvedTy::Function {
                                params: vec![int],
                                return_ty: ResolvedTy::Void.into(),
                            }
                            .into(),
                        },
                        56..112,
                        None,
                    ),
                    (
                        TyDiagnosticKind::MismatchedArgCount {
                            found: 1,
                            expected: 2,
                        },
                        87..93,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: float,
                            found: int,
                        },
                        91..92,
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
                0 : i32
                1 : i32
                2 : <unknown>
                3 : void
            "#]],
            |_| {
                let int = ResolvedTy::IInt(32).into();
                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: int,
                            found: ResolvedTy::Function {
                                params: vec![int],
                                return_ty: ResolvedTy::Void.into(),
                            }
                            .into(),
                        },
                        29..85,
                        None,
                    ),
                    (
                        TyDiagnosticKind::CalledNonFunction { found: int },
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
                foo :: (arg: bool) -> string {
                    if arg {
                        "hello"
                    }
                };
            "#,
            expect![[r#"
                main::foo : (bool) -> string
                0 : bool
                1 : string
                2 : string
                3 : string
                4 : string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MissingElse {
                        expected: ResolvedTy::String.into(),
                    },
                    68..130,
                    Some((
                        TyDiagnosticHelpKind::IfReturnsTypeHere {
                            found: ResolvedTy::String.into(),
                        },
                        101..108,
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
                l0 : type
                l1 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::LocalTyIsMutable,
                    106..115,
                    Some((TyDiagnosticHelpKind::MutableVariable, 49..74)),
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
                3 : type
                5 : {uint}
                6 : void
                l0 : type
                l1 : type
                l2 : {uint}
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::LocalTyIsMutable,
                    108..117,
                    Some((TyDiagnosticHelpKind::MutableVariable, 49..74)),
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
                l0 : i8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IntTooBigForType {
                        found: 128,
                        max: 127,
                        ty: ResolvedTy::IInt(8).into(),
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
                1 : i8
                3 : i8
                4 : void
                l0 : i8
                l1 : i8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IntTooBigForType {
                        found: 128,
                        max: 127,
                        ty: ResolvedTy::IInt(8).into(),
                    },
                    59..62,
                    None,
                )]
            },
        );
    }

    #[test]
    fn struct_literal() {
        check(
            r#"
                Person :: struct {
                    name: string,
                    age: i32
                };

                foo :: () {
                    some_guy := Person {
                        name: "Joe Schmoe",
                        age: 31,
                    };
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                0 : type
                3 : string
                4 : i32
                5 : main::Person
                6 : void
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
                    name: string,
                    age: i32
                };

                foo :: () {
                    some_guy := Person {
                        name: false,
                        height: "5'9\""
                    };
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> void
                0 : type
                3 : bool
                4 : string
                5 : main::Person
                6 : void
                l0 : main::Person
            "#]],
            |i| {
                let person_ty = ResolvedTy::Struct {
                    fqn: Some(hir::Fqn {
                        module: hir::FileName(i.intern("main.capy")),
                        name: hir::Name(i.intern("Person")),
                    }),
                    fields: vec![
                        (hir::Name(i.intern("name")), ResolvedTy::String.into()),
                        (hir::Name(i.intern("age")), ResolvedTy::IInt(32).into()),
                    ],
                }
                .into();

                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: ResolvedTy::String.into(),
                            found: ResolvedTy::Bool.into(),
                        },
                        218..223,
                        None,
                    ),
                    (
                        TyDiagnosticKind::NonExistentField {
                            field: i.intern("height"),
                            found_ty: person_ty,
                        },
                        249..255,
                        None,
                    ),
                    (
                        TyDiagnosticKind::StructLiteralMissingField {
                            field: i.intern("age"),
                            expected_ty: person_ty,
                        },
                        179..286,
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
                    name: string,
                    age: i32
                };

                foo :: () -> i32 {
                    some_guy := Person {
                        name: "Joe Schmoe",
                        age: 31,
                    };

                    some_guy.age
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> i32
                0 : type
                3 : string
                4 : i32
                5 : main::Person
                6 : main::Person
                7 : i32
                8 : i32
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
                    name: string,
                    age: i32
                };

                foo :: () -> i32 {
                    some_guy := Person {
                        name: "Joe Schmoe",
                        age: 31,
                    };

                    some_guy.height
                };
            "#,
            expect![[r#"
                main::Person : type
                main::foo : () -> i32
                0 : type
                3 : string
                4 : i32
                5 : main::Person
                6 : main::Person
                7 : <unknown>
                8 : <unknown>
                l0 : main::Person
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NonExistentField {
                        field: i.intern("height"),
                        found_ty: ResolvedTy::Struct {
                            fqn: Some(hir::Fqn {
                                module: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Person")),
                            }),
                            fields: vec![
                                (hir::Name(i.intern("name")), ResolvedTy::String.into()),
                                (hir::Name(i.intern("age")), ResolvedTy::IInt(32).into()),
                            ],
                        }
                        .into(),
                    },
                    316..331,
                    None,
                )]
            },
        );
    }

    #[test]
    fn if_mismatch() {
        check(
            r#"
                foo :: (bar: bool) {
                    if bar {
                        "Hello!"
                    } else {
                        100
                    };
                };
            "#,
            expect![[r#"
                main::foo : (bool) -> void
                0 : bool
                1 : string
                2 : string
                3 : {uint}
                4 : {uint}
                5 : string
                6 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IfMismatch {
                        found: ResolvedTy::UInt(0).into(),
                        expected: ResolvedTy::String.into(),
                    },
                    58..178,
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
                1 : string
                2 : string
                3 : {uint}
                4 : <unknown>
                5 : void
                l0 : string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexNonArray {
                        found: ResolvedTy::String.into(),
                    },
                    87..93,
                    None,
                )]
            },
        );
    }

    #[test]
    fn mismatch_arg_count() {
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
                0 : void
                1 : (i32) -> void
                2 : i32
                3 : {uint}
                4 : {uint}
                5 : void
                6 : void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MismatchedArgCount {
                        found: 3,
                        expected: 1,
                    },
                    88..100,
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
                1 : string
                2 : string
                3 : {uint}
                4 : <unknown>
                5 : void
                l0 : string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CalledNonFunction {
                        found: ResolvedTy::String.into(),
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
                1 : string
                2 : string
                3 : <unknown>
                4 : void
                l0 : string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::DerefNonPointer {
                        found: ResolvedTy::String.into(),
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
                1 : string
                2 : void
                l0 : string
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

                    real as imaginary;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                3 : i32
                4 : i32
                6 : distinct'0 i32
                7 : void
                l0 : type
                l1 : i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn array_with_local_ty() {
        check(
            r#"
                foo :: () {
                    imaginary :: distinct i32;

                    array := [] imaginary { 1, 2, 3 };
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : type
                4 : {uint}
                5 : {uint}
                6 : {uint}
                7 : [3]distinct'0 i32
                8 : void
                l0 : type
                l1 : [3]distinct'0 i32
            "#]],
            |_| [],
        );
    }

    #[test]
    fn lambda_ty_annotation() {
        check(
            r#"
                bar :: (s: string) {
                    // do stuff
                } 

                foo :: () {
                    a : (s: string) -> void = (s: string) {};

                    a = bar;

                    a("Hello!");
                }
            "#,
            expect![[r#"
                main::bar : (string) -> void
                main::foo : () -> void
                0 : void
                2 : void
                3 : (string) -> void
                4 : (string) -> void
                5 : (string) -> void
                6 : (string) -> void
                7 : string
                8 : void
                9 : void
                l0 : (string) -> void
            "#]],
            |_| [],
        );
    }

    #[test]
    fn lambda_with_body_ty_annotation() {
        check(
            r#"
                foo :: () {
                    a : (s: string) -> void {} = (s: string) {};

                    a("Hello!");
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : (string) -> void
                2 : void
                3 : (string) -> void
                4 : (string) -> void
                5 : string
                6 : void
                7 : void
                l0 : (string) -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::Type.into(),
                        found: ResolvedTy::Function {
                            params: vec![ResolvedTy::String.into()],
                            return_ty: ResolvedTy::Void.into(),
                        }
                        .into(),
                    },
                    53..75,
                    None,
                )]
            },
        );
    }

    #[test]
    fn comptime() {
        check(
            r#"
                foo :: () {
                    foo : string = comptime {
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
                l0 : string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Intern::new(ResolvedTy::String),
                        found: Intern::new(ResolvedTy::UInt(0)),
                    },
                    64..126,
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
                1 : {uint}
                2 : {uint}
                3 : ^{uint}
                4 : ^{uint}
                5 : <unknown>
                6 : void
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
    fn any_type() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;

                    ptr : ^i32 = ^foo;
                    ptr : ^any = ptr as ^any;
                    ptr : ^f32 = ptr as ^f32;

                    foo : f32 = ptr^;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                3 : i32
                4 : ^i32
                6 : ^i32
                8 : ^any
                10 : ^any
                12 : ^f32
                14 : ^f32
                15 : f32
                16 : void
                l0 : i32
                l1 : ^i32
                l2 : ^any
                l3 : ^f32
                l4 : f32
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
                    ptr : ^f32 = ptr as ^f32;

                    foo : f32 = ptr^;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                3 : i32
                4 : ^i32
                6 : ^i32
                8 : ^f32
                10 : ^f32
                11 : f32
                12 : void
                l0 : i32
                l1 : ^i32
                l2 : ^f32
                l3 : f32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
                        to: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: ResolvedTy::Float(32).into(),
                        }
                        .into(),
                    },
                    141..152,
                    None,
                )]
            },
        );
    }

    #[test]
    fn deref_any() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;

                    ptr : ^i32 = ^foo;
                    ptr : ^any = ptr as ^any;

                    foo : any = ptr^;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                3 : i32
                4 : ^i32
                6 : ^i32
                8 : ^any
                10 : ^any
                11 : <unknown>
                12 : void
                l0 : i32
                l1 : ^i32
                l2 : ^any
                l3 : any
            "#]],
            |_| [(TyDiagnosticKind::DerefAny, 187..191, None)],
        );
    }

    #[test]
    fn auto_real_ptr_to_any_ptr() {
        check(
            r#"
                get_any :: () {
                    foo : i32 = 5;
                    ptr : ^i32 = ^foo;

                    ptr : ^any = ptr;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                3 : i32
                4 : ^i32
                6 : ^i32
                7 : void
                l0 : i32
                l1 : ^i32
                l2 : ^any
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
                    ptr : ^any = ptr;

                    ptr : ^i32 = ptr;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : i32
                3 : i32
                4 : ^i32
                6 : ^i32
                8 : ^any
                9 : void
                l0 : i32
                l1 : ^i32
                l2 : ^any
                l3 : ^i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: ResolvedTy::IInt(32).into(),
                        }
                        .into(),
                        found: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: ResolvedTy::Any.into(),
                        }
                        .into(),
                    },
                    179..182,
                    None,
                )]
            },
        );
    }

    #[test]
    fn any_ptr_to_string() {
        check(
            r#"
                get_any :: () {
                    bytes := [3] u8 { 72, 73, 0 };
                    ptr := {^bytes} as ^any;
                    str := ptr as string;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                2 : u8
                3 : u8
                4 : u8
                5 : [3]u8
                7 : [3]u8
                8 : ^[3]u8
                9 : ^[3]u8
                11 : ^any
                13 : ^any
                15 : string
                16 : void
                l0 : [3]u8
                l1 : ^any
                l2 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn u8_ptr_to_string() {
        check(
            r#"
                get_any :: () {
                    bytes := [3] u8 { 72, 73, 0 };
                    ptr := {{^bytes} as ^any} as ^u8;
                    str := ptr as string;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                2 : u8
                3 : u8
                4 : u8
                5 : [3]u8
                7 : [3]u8
                8 : ^[3]u8
                9 : ^[3]u8
                11 : ^any
                12 : ^any
                14 : ^u8
                16 : ^u8
                18 : string
                19 : void
                l0 : [3]u8
                l1 : ^u8
                l2 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn field_of_struct_ptr() {
        check(
            r#"
                Foo :: struct {
                    a: i32
                };

                main :: () {
                    my_foo := Foo {
                        a: 25
                    };

                    ptr := ^my_foo;

                    ptr.a;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                0 : type
                3 : i32
                4 : main::Foo
                6 : main::Foo
                7 : ^main::Foo
                8 : ^main::Foo
                9 : i32
                10 : void
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
                    my_foo := Foo {
                        a: 25
                    };

                    ptr := ^^my_foo;

                    ptr.a;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                0 : type
                3 : i32
                4 : main::Foo
                6 : main::Foo
                7 : ^main::Foo
                8 : ^^main::Foo
                9 : ^^main::Foo
                10 : i32
                11 : void
                l0 : main::Foo
                l1 : ^^main::Foo
            "#]],
            |_| [],
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
                    my_foo := Foo {
                        a: 25
                    };

                    ptr := ^^my_foo;

                    ptr.b;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                0 : type
                3 : i32
                4 : main::Foo
                6 : main::Foo
                7 : ^main::Foo
                8 : ^^main::Foo
                9 : ^^main::Foo
                10 : <unknown>
                11 : void
                l0 : main::Foo
                l1 : ^^main::Foo
            "#]],
            |i| {
                [(
                    TyDiagnosticKind::NonExistentField {
                        field: i.intern("b"),
                        found_ty: ResolvedTy::Pointer {
                            mutable: false,
                            sub_ty: ResolvedTy::Pointer {
                                mutable: false,
                                sub_ty: ResolvedTy::Struct {
                                    fqn: Some(hir::Fqn {
                                        module: hir::FileName(i.intern("main.capy")),
                                        name: hir::Name(i.intern("Foo")),
                                    }),
                                    fields: vec![(
                                        hir::Name(i.intern("a")),
                                        ResolvedTy::IInt(32).into(),
                                    )],
                                }
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    257..262,
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
                    my_foo := Foo {
                        a: 25
                    };

                    ptr := ^mut ^mut my_foo;

                    ptr.a = 5;
                }
            "#,
            expect![[r#"
                main::Foo : type
                main::main : () -> void
                0 : type
                3 : i32
                4 : main::Foo
                6 : main::Foo
                7 : ^mut main::Foo
                8 : ^mut ^mut main::Foo
                9 : ^mut ^mut main::Foo
                10 : i32
                11 : i32
                12 : void
                l0 : main::Foo
                l1 : ^mut ^mut main::Foo
            "#]],
            |_| [],
        );
    }
}

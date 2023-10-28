mod ctx;
mod ty;

use hir::FileName;
use interner::{Interner, Key};
use internment::Intern;
use itertools::Itertools;
use la_arena::{ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use text_size::TextRange;

pub use ty::*;

#[derive(Clone)]
pub struct InferenceResult {
    signatures: FxHashMap<hir::Fqn, Signature>,
    files: FxHashMap<hir::FileName, ModuleInference>,
}

#[derive(Debug, Clone)]
pub struct ModuleInference {
    expr_tys: ArenaMap<Idx<hir::Expr>, Intern<Ty>>,
    /// the actual types of type expressions
    meta_tys: ArenaMap<Idx<hir::Expr>, Intern<Ty>>,
    local_tys: ArenaMap<Idx<hir::LocalDef>, Intern<Ty>>,
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
        &self.files[&module]
    }
}

impl ModuleInference {
    pub fn get_meta_ty(&self, expr: Idx<hir::Expr>) -> Option<Intern<Ty>> {
        self.meta_tys.get(expr).copied()
    }
}

impl std::ops::Index<Idx<hir::Expr>> for ModuleInference {
    type Output = Intern<Ty>;

    fn index(&self, expr: Idx<hir::Expr>) -> &Self::Output {
        &self.expr_tys[expr]
    }
}

impl std::ops::Index<Idx<hir::LocalDef>> for ModuleInference {
    type Output = Intern<Ty>;

    fn index(&self, local_def: Idx<hir::LocalDef>) -> &Self::Output {
        &self.local_tys[local_def]
    }
}

#[derive(Debug, Clone)]
pub struct Signature(pub Intern<Ty>);

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
        expected: Intern<Ty>,
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
        found: Intern<Ty>,
        expected: Intern<Ty>,
    },
    IndexNonArray {
        found: Intern<Ty>,
    },
    IndexOutOfBounds {
        index: u64,
        actual_size: u64,
        array_ty: Intern<Ty>,
    },
    MismatchedArgCount {
        found: usize,
        expected: usize,
    },
    CalledNonFunction {
        found: Intern<Ty>,
    },
    DerefNonPointer {
        found: Intern<Ty>,
    },
    DerefAny,
    MissingElse {
        expected: Intern<Ty>,
    },
    CannotMutate,
    MutableRefToImmutableData,
    NotYetResolved {
        fqn: hir::Fqn,
    },
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
    NonExistentField {
        field: Key,
        found_ty: Intern<Ty>,
    },
    StructLiteralMissingField {
        field: Key,
        expected_ty: Intern<Ty>,
    },
    ComptimePointer,
    ComptimeType,
    GlobalNotConst,
    EntryNotFunction,
    EntryHasParams,
    EntryBadReturn,
    ArraySizeRequired,
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

#[derive(Debug)]
pub struct InferenceCtx<'a> {
    current_file: Option<hir::FileName>,
    bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
    world_index: &'a hir::WorldIndex,
    local_usages: FxHashMap<hir::FileName, ArenaMap<Idx<hir::LocalDef>, FxHashSet<LocalUsage>>>,
    param_tys: Option<Vec<Intern<Ty>>>,
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
    ) -> InferenceCtx<'a> {
        Self {
            current_file: None,
            bodies_map,
            world_index,
            local_usages: FxHashMap::default(),
            param_tys: None,
            diagnostics: Vec::new(),
            signatures: FxHashMap::default(),
            modules: FxHashMap::default(),
        }
    }

    /// only pass `None` to `entry_point` if your testing type checking and you don't want to worry
    /// about the entry point
    pub fn finish(mut self, entry_point: Option<hir::Fqn>) -> (InferenceResult, Vec<TyDiagnostic>) {
        for (module, _) in self.world_index.get_all_files() {
            self.modules.insert(
                module,
                ModuleInference {
                    expr_tys: ArenaMap::default(),
                    meta_tys: ArenaMap::default(),
                    local_tys: ArenaMap::default(),
                },
            );
        }

        for (file, index) in self.world_index.get_all_files() {
            for name in index.definition_names() {
                let fqn = hir::Fqn { file, name };

                if !self.signatures.contains_key(&fqn) {
                    self.get_signature(fqn);
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

                let ty = self.get_signature(entry_point).0;

                if let Some((param_tys, return_ty)) = ty.as_function() {
                    let lambda = match self.bodies_map[&entry_point.file]
                        [self.bodies_map[&entry_point.file].global_body(entry_point.name)]
                    {
                        hir::Expr::Lambda(lambda) => &self.bodies_map[&entry_point.file][lambda],
                        _ => todo!("entry point doesn't have lambda body"),
                    };

                    if !param_tys.is_empty() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::EntryHasParams,
                            module: entry_point.file,
                            range: lambda.params_range,
                            help: None,
                        });
                    }

                    if !return_ty.is_void() && !return_ty.is_int() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::EntryBadReturn,
                            module: entry_point.file,
                            // unwrap is safe because if the return type didn't exist, it'd be void
                            range: self.bodies_map[&entry_point.file]
                                .range_for_expr(lambda.return_ty.unwrap()),
                            help: None,
                        });
                    }
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::EntryNotFunction,
                        module: entry_point.file,
                        range: range.whole,
                        help: None,
                    });
                }
            }
        }

        let mut result = InferenceResult {
            signatures: self.signatures,
            files: self.modules,
        };
        result.shrink_to_fit();

        (result, self.diagnostics)
    }

    fn get_signature(&mut self, fqn: hir::Fqn) -> Signature {
        if let Some(sig) = self.signatures.get(&fqn) {
            return sig.clone();
        }

        let old_module = self.current_file.replace(fqn.file);

        // we do this before parsing the possible type annotation
        // to avoid a stack overflow like this:
        // a : a : 5;
        self.signatures
            .insert(fqn, Signature(Intern::new(Ty::NotYetResolved)));

        let body = self.bodies_map[&self.current_file.unwrap()].global_body(fqn.name);

        // if there's a type annotation to the global, make sure it matches the type of the body
        let ty_annotation = self.bodies_map[&self.current_file.unwrap()]
            .global_ty(fqn.name)
            .map(|ty| self.parse_expr_to_ty(ty, &mut FxHashSet::default()));

        // we parse global functions differently to allow recursion
        let ty = match &self.bodies_map[&self.current_file.unwrap()][body] {
            hir::Expr::Lambda(lambda) => {
                let ty = if let Some(ty_annotation) = ty_annotation {
                    self.signatures.insert(fqn, Signature(ty_annotation));

                    let ty = self.infer_lambda(body, *lambda, None);

                    self.expect_match(ty, ty_annotation, body);

                    ty
                } else {
                    self.infer_lambda(body, *lambda, Some(fqn))
                };

                self.modules
                    .get_mut(&self.current_file.unwrap())
                    .unwrap()
                    .expr_tys
                    .insert(body, ty);

                ty
            }
            _ => {
                let ty = self.finish_body(body, None, ty_annotation, true);

                self.signatures.insert(fqn, Signature(ty));

                ty
            }
        };

        self.current_file = old_module;

        Signature(ty)
    }

    fn infer_lambda(
        &mut self,
        expr: Idx<hir::Expr>,
        lambda: Idx<hir::Lambda>,
        fqn: Option<hir::Fqn>,
    ) -> Intern<Ty> {
        let hir::Lambda {
            params,
            return_ty,
            body,
            is_extern,
            ..
        } = &self.bodies_map[&self.current_file.unwrap()][lambda];

        let return_ty = if let Some(return_ty) = return_ty {
            self.parse_expr_to_ty(*return_ty, &mut FxHashSet::default())
        } else {
            Ty::Void.into()
        };

        let param_tys = params
            .iter()
            .map(|param| self.parse_expr_to_ty(param.ty, &mut FxHashSet::default()))
            .collect::<Vec<_>>();

        let ty = Ty::Function {
            param_tys: param_tys.clone(),
            return_ty,
        }
        .into();

        if !is_extern && self.bodies_map[&self.current_file.unwrap()][*body] == hir::Expr::Missing {
            self.modules
                .get_mut(&self.current_file.unwrap())
                .unwrap()
                .meta_tys
                .insert(expr, ty);

            return Ty::Type.into();
        }

        // this allows recursion
        if let Some(fqn) = fqn {
            self.signatures.insert(fqn, Signature(ty));
        }

        if !is_extern {
            self.finish_body(*body, Some(param_tys), Some(return_ty), false);
        }

        ty
    }

    fn fqn_to_ty(
        &mut self,
        fqn: hir::Fqn,
        module_range: Option<TextRange>,
        name_range: TextRange,
        resolve_chain: &mut FxHashSet<hir::Fqn>,
    ) -> Intern<Ty> {
        // this makes sure we don't stack overflow on recursion
        if !resolve_chain.insert(fqn) {
            return Ty::Unknown.into();
        }

        match self.world_index.get_definition(fqn) {
            Ok(_) => {
                let ty = self.get_signature(fqn).0;

                if *ty == Ty::Unknown {
                    return Ty::Unknown.into();
                }

                if *ty == Ty::NotYetResolved {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::NotYetResolved { fqn },
                        module: self.current_file.unwrap(),
                        range: name_range,
                        help: None,
                    });

                    return Ty::Unknown.into();
                }

                if *ty != Ty::Type {
                    if !ty.is_unknown() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::Mismatch {
                                expected: Ty::Type.into(),
                                found: ty,
                            },
                            module: self.current_file.unwrap(),
                            range: name_range,
                            help: None,
                        });
                    }
                    return Ty::Unknown.into();
                }

                let global_body = self.bodies_map[&fqn.file].global_body(fqn.name);

                let old_module = self.current_file.replace(fqn.file);

                let actual_ty = self.parse_expr_to_ty(global_body, resolve_chain);

                self.current_file = old_module;

                // it'd be better to mutate the fqn, but that would invalidate the hash
                // within the internment crate
                match actual_ty.as_ref() {
                    Ty::Distinct { fqn: None, ty, uid } => Ty::Distinct {
                        fqn: Some(fqn),
                        uid: *uid,
                        ty: *ty,
                    }
                    .into(),
                    Ty::Struct {
                        fqn: None,
                        fields,
                        uid,
                    } => Ty::Struct {
                        fqn: Some(fqn),
                        fields: fields.clone(),
                        uid: *uid,
                    }
                    .into(),
                    _ => actual_ty,
                }
            }
            Err(hir::GetDefinitionError::UnknownFile) => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFile { file: fqn.file },
                    module: self.current_file.unwrap(),
                    range: module_range.unwrap(),
                    help: None,
                });
                Ty::Unknown.into()
            }
            Err(hir::GetDefinitionError::UnknownDefinition) => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFqn { fqn },
                    module: self.current_file.unwrap(),
                    range: name_range,
                    help: None,
                });
                Ty::Unknown.into()
            }
        }
    }

    fn parse_expr_to_ty(
        &mut self,
        expr: Idx<hir::Expr>,
        resolve_chain: &mut FxHashSet<hir::Fqn>,
    ) -> Intern<Ty> {
        if let Some(meta_ty) = self.modules[&self.current_file.unwrap()].get_meta_ty(expr) {
            return meta_ty;
        }

        let ty = match &self.bodies_map[&self.current_file.unwrap()][expr] {
            hir::Expr::Missing => Ty::Unknown.into(),
            hir::Expr::Ref { mutable, expr } => {
                let sub_ty = self.parse_expr_to_ty(*expr, resolve_chain);

                Ty::Pointer {
                    mutable: *mutable,
                    sub_ty,
                }
                .into()
            }
            hir::Expr::Local(local_def) => {
                let local_ty = self.modules[&self.current_file.unwrap()].local_tys[*local_def];

                if *local_ty == Ty::Unknown {
                    return Ty::Unknown.into();
                }

                if *local_ty != Ty::Type {
                    if !local_ty.is_unknown() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::Mismatch {
                                expected: Ty::Type.into(),
                                found: self.modules[&self.current_file.unwrap()].local_tys
                                    [*local_def],
                            },
                            module: self.current_file.unwrap(),
                            range: self.bodies_map[&self.current_file.unwrap()]
                                .range_for_expr(expr),
                            help: None,
                        });
                    }

                    return Ty::Unknown.into();
                }

                let local_def = &self.bodies_map[&self.current_file.unwrap()][*local_def];

                if local_def.mutable {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::LocalTyIsMutable,
                        module: self.current_file.unwrap(),
                        range: self.bodies_map[&self.current_file.unwrap()].range_for_expr(expr),
                        help: Some(TyDiagnosticHelp {
                            kind: TyDiagnosticHelpKind::MutableVariable,
                            range: local_def.range,
                        }),
                    });

                    return Ty::Unknown.into();
                }

                self.parse_expr_to_ty(local_def.value, resolve_chain)
            }
            hir::Expr::LocalGlobal(name) => self.fqn_to_ty(
                hir::Fqn {
                    file: self.current_file.unwrap(),
                    name: name.name,
                },
                None,
                name.range,
                resolve_chain,
            ),
            hir::Expr::Param { .. } => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::ParamNotATy,
                    module: self.current_file.unwrap(),
                    range: self.bodies_map[&self.current_file.unwrap()].range_for_expr(expr),
                    help: None,
                });

                Ty::Unknown.into()
            }
            hir::Expr::Path { previous, field } => {
                let previous_ty = self.infer_expr(*previous);
                match previous_ty.as_ref() {
                    Ty::File(file) => self.fqn_to_ty(
                        hir::Fqn {
                            file: *file,
                            name: field.name,
                        },
                        Some(
                            self.bodies_map[&self.current_file.unwrap()].range_for_expr(*previous),
                        ),
                        field.range,
                        resolve_chain,
                    ),
                    _ => {
                        let expr_ty = self.infer_expr(expr);
                        if !expr_ty.is_unknown() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Mismatch {
                                    expected: Ty::Type.into(),
                                    found: expr_ty,
                                },
                                module: self.current_file.unwrap(),
                                range: self.bodies_map[&self.current_file.unwrap()]
                                    .range_for_expr(expr),
                                help: None,
                            });
                        }

                        Ty::Unknown.into()
                    }
                }
            }
            hir::Expr::PrimitiveTy(ty) => Ty::from_primitive(*ty).into(),
            hir::Expr::Array {
                size,
                items: None,
                ty,
            } => {
                let sub_ty = self.parse_expr_to_ty(*ty, resolve_chain);

                if let Some(size) = size {
                    Ty::Array {
                        size: *size,
                        sub_ty,
                    }
                    .into()
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ArraySizeRequired,
                        module: self.current_file.unwrap(),
                        range: self.bodies_map[&self.current_file.unwrap()].range_for_expr(expr),
                        help: None,
                    });

                    Ty::Unknown.into()
                }
            }
            hir::Expr::Distinct { uid, ty } => Ty::Distinct {
                fqn: None,
                uid: *uid,
                ty: self.parse_expr_to_ty(*ty, resolve_chain),
            }
            .into(),
            hir::Expr::StructDecl { uid, fields } => Ty::Struct {
                fqn: None,
                uid: *uid,
                fields: fields
                    .iter()
                    .cloned()
                    .filter_map(|(name, ty)| name.map(|name| (name, ty)))
                    .map(|(name, ty)| {
                        (
                            name.name,
                            self.parse_expr_to_ty(ty, &mut resolve_chain.clone()),
                        )
                    })
                    .collect(),
            }
            .into(),
            hir::Expr::Lambda(lambda) => {
                let hir::Lambda {
                    params,
                    return_ty,
                    body,
                    is_extern,
                    ..
                } = &self.bodies_map[&self.current_file.unwrap()][*lambda];

                let return_ty = if let Some(return_ty) = return_ty {
                    self.parse_expr_to_ty(*return_ty, resolve_chain)
                } else {
                    Ty::Void.into()
                };

                let param_tys = params
                    .iter()
                    .map(|param| self.parse_expr_to_ty(param.ty, resolve_chain))
                    .collect::<Vec<_>>();

                let ty = Ty::Function {
                    param_tys: param_tys.clone(),
                    return_ty,
                }
                .into();

                // if the function has a body (or is extern), then it isn't a type
                if *is_extern
                    || self.bodies_map[&self.current_file.unwrap()][*body] != hir::Expr::Missing
                {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::Mismatch {
                            expected: Ty::Type.into(),
                            found: ty,
                        },
                        module: self.current_file.unwrap(),
                        range: self.bodies_map[&self.current_file.unwrap()].range_for_expr(expr),
                        help: None,
                    });

                    return Ty::Unknown.into();
                }

                ty
            }
            _ => {
                let expr_ty = self.infer_expr(expr);
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::Mismatch {
                        expected: Ty::Type.into(),
                        found: expr_ty,
                    },
                    module: self.current_file.unwrap(),
                    range: self.bodies_map[&self.current_file.unwrap()].range_for_expr(expr),
                    help: None,
                });

                Ty::Unknown.into()
            }
        };

        self.modules
            .get_mut(&self.current_file.unwrap())
            .unwrap()
            .meta_tys
            .insert(expr, ty);

        ty
    }
}

impl InferenceResult {
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

    pub fn debug(&self, mod_dir: &std::path::Path, interner: &Interner, fancy: bool) -> String {
        let mut s = String::new();

        let mut signatures = self
            .signatures
            .iter()
            .map(|(fqn, sig)| (fqn.to_string(mod_dir, interner), sig))
            .collect::<Vec<_>>();

        signatures.sort_by(|(fqn1, _), (fqn2, _)| fqn1.cmp(fqn2));

        for (fqn, sig) in signatures {
            s.push_str(&fqn);
            s.push_str(" : ");
            s.push_str(&format!("{}\n", sig.0.display(mod_dir, interner)));
        }

        let mut files = self.files.iter().collect::<Vec<_>>();
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
            Self::Char => "char".to_string(),
            Self::Array { size, sub_ty } => {
                format!("[{size}]{}", sub_ty.display(mod_dir, interner))
            }
            Self::Pointer { mutable, sub_ty } => {
                format!(
                    "^{}{}",
                    if *mutable { "mut " } else { "" },
                    sub_ty.display(mod_dir, interner)
                )
            }
            Self::Distinct { fqn: Some(fqn), .. } => fqn.to_string(mod_dir, interner),
            Self::Distinct { fqn: None, uid, ty } => {
                format!("distinct'{} {}", uid, ty.display(mod_dir, interner))
            }
            Self::Function {
                param_tys: params,
                return_ty,
            } => {
                let mut res = "(".to_string();

                for (idx, param) in params.iter().enumerate() {
                    res.push_str(&param.display(mod_dir, interner));

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
                fqn: None,
                uid,
                fields,
            } => {
                let mut res = format!("struct'{} {{", uid);

                for (idx, (name, ty)) in fields.iter().enumerate() {
                    res.push_str(interner.lookup(name.0));
                    res.push_str(": ");

                    res.push_str(&ty.display(mod_dir, interner));

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
            Self::File(file_name) => {
                format!("file {}", file_name.to_string(mod_dir, interner))
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
        check_with_entry(input, expect, expected_diagnostics, None)
    }

    fn check_with_entry<const N: usize>(
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
        let mut bodies_map = FxHashMap::default();

        for (name, text) in &modules {
            if *name == "main.capy" {
                continue;
            }

            let tokens = lexer::lex(text);
            let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
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
            world_index.add_file(module, index);
            bodies_map.insert(module, bodies);
        }

        let text = &modules["main.capy"];
        let module = hir::FileName(interner.intern("main.capy"));
        let tokens = lexer::lex(text);
        let tree = parser::parse_source_file(&tokens, text).into_syntax_tree();
        let root = ast::Root::cast(tree.root(), &tree).unwrap();
        let (index, _) = hir::index(root, &tree, &mut interner);

        let (bodies, _) = hir::lower(
            root,
            &tree,
            Path::new("main"),
            &index,
            &mut uid_gen,
            &mut interner,
            Path::new(""),
            true,
        );
        world_index.add_file(module, index);
        bodies_map.insert(module, bodies);

        let (inference_result, actual_diagnostics) = InferenceCtx::new(&bodies_map, &world_index)
            .finish(entry_point.map(|entry_point| hir::Fqn {
                file: module,
                name: hir::Name(interner.intern(entry_point)),
            }));

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

        let expected_diagnostics = format!("{:#?}", expected_diagnostics);
        let actual_diagnostics = format!("{:#?}", actual_diagnostics);

        let (dist, changeset) = text_diff::diff(&expected_diagnostics, &actual_diagnostics, "");

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
                expected_diagnostics, actual_diagnostics, diff
            );

            panic!("expected diagnostics are not equal to actual diagnostics");
        }
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
    fn ty_in_other_module() {
        check(
            r#"
                #- main.capy
                numbers :: import "numbers.capy";

                fun :: () -> numbers.imaginary {
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
                    num1 := 4 as i128;
                    num2 := 8 as u16;
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
                    is_true := num as bool;
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
                    age := name as usize;
                    age
                };
            "#,
            expect![[r#"
                main::how_old : () -> usize
                1 : string
                2 : string
                4 : usize
                5 : usize
                6 : usize
                7 : () -> usize
                l0 : string
                l1 : usize
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Uncastable {
                        from: Ty::String.into(),
                        to: Ty::UInt(u32::MAX).into(),
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
                    my_array := [] i32 { 4, 8, 15, 16, 23, 42 };
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
    fn array_with_size() {
        check(
            r#"
                main :: () {
                    my_array := [6] i32 { 4, 8, 15, 16, 23, 42 };
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
    fn array_with_incorrect_size() {
        check(
            r#"
                main :: () {
                    my_array := [7] i32 { 4, 8, 15, 16, 23, 42 };
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
                7 : [7]i32
                8 : void
                9 : () -> void
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
                13 : () -> i32
                l0 : [6]i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IndexOutOfBounds {
                        index: 1000,
                        actual_size: 6,
                        array_ty: Ty::Array {
                            size: 6,
                            sub_ty: Ty::IInt(32).into(),
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
                1 : u8
                2 : bool
                3 : u8
                4 : u8
                5 : u8
                6 : u8
                7 : u8
                8 : u8
                9 : u8
                10 : u8
                11 : u8
                12 : () -> u8
                l0 : u8
                l1 : u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::UInt(8).into(),
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
                1 : string
                2 : string
                3 : void
                4 : () -> void
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
                0 : string
                1 : string
                2 : string
                3 : string
                4 : void
                5 : () -> void
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
                        expected: Ty::UInt(8).into(),
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
                        expected: Ty::UInt(16).into(),
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
                        expected: Ty::UInt(16).into(),
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
                        expected: Ty::UInt(8).into(),
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
                1 : string
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
                f :: () -> string { "hello" + };
            "#,
            expect![[r#"
                main::f : () -> string
                1 : string
                2 : <unknown>
                3 : string
                4 : string
                5 : () -> string
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
                1 : string
                2 : string
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
                1 : u8
                2 : u8
                3 : u8
                4 : () -> u8
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::UInt(8).into(),
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
                s :: () -> string { 92 };
            "#,
            expect![[r#"
                main::s : () -> string
                1 : {uint}
                2 : {uint}
                3 : () -> string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::String.into(),
                        found: Ty::UInt(0).into(),
                    },
                    35..41,
                    Some((TyDiagnosticHelpKind::TailExprReturnsHere, 37..39)),
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
                3 : string
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
                            expected: Ty::IInt(32).into(),
                            found: Ty::Void.into(),
                        },
                        46..48,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: Ty::IInt(32).into(),
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
                  2 : string
                  3 : string
                  4 : (i32) -> string
                main:
                  1 : file greetings
                  2 : file greetings
                  3 : (i32) -> string
                  4 : i32
                  5 : string
                  6 : string
                  7 : () -> string
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
                4 : string
                5 : string
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
                        expected: Ty::IInt(32).into(),
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
                        expected: Ty::IInt(32).into(),
                        found: Ty::Distinct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("imaginary")),
                            }),
                            uid: 0,
                            ty: Ty::IInt(32).into(),
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
                            ty: Ty::IInt(32).into(),
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
                            ty: Ty::IInt(32).into(),
                        }
                        .into(),
                        second: Ty::Distinct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("extra_imaginary")),
                            }),
                            uid: 1,
                            ty: Ty::IInt(32).into(),
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
                2 : type
                5 : i32
                6 : main::something_far_away
                7 : main::something_far_away
                10 : ^i32
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

                    {x as ^imaginary}^
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
                14 : ^main::imaginary
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
                    my_point : Vector3 = [] i32 { 4, 8, 15 };

                    x := my_point[0];
                    y := my_point[1];
                    z := my_point[2];
                };
            "#,
            expect![[r#"
                main::Vector3 : type
                main::main : () -> void
                2 : type
                5 : i32
                6 : i32
                7 : i32
                8 : [3]i32
                9 : main::Vector3
                10 : usize
                11 : i32
                12 : main::Vector3
                13 : usize
                14 : i32
                15 : main::Vector3
                16 : usize
                17 : i32
                18 : void
                19 : () -> void
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
            |i| {
                [(
                    TyDiagnosticKind::NotYetResolved {
                        fqn: hir::Fqn {
                            file: hir::FileName(i.intern("main.capy")),
                            name: hir::Name(i.intern("foo")),
                        },
                    },
                    77..80,
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
                }
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
    fn recursive_struct_and_multiple_instances() {
        // this is handled in hir lowering
        check(
            r#"
                Foo :: struct {
                    bar: Foo,
                };

                global_foo :: comptime {
                    Foo { bar: 0 }
                };

                main :: () {
                    my_foo := Foo {
                        bar: true,
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
                1 : type
                3 : {uint}
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
                2 : type
                4 : string
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
                2 : type
                4 : string
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
                    297..319,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 167..275)),
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
                2 : type
                5 : type
                9 : string
                10 : i32
                11 : main::Person
                13 : string
                14 : i32
                15 : main::Person
                17 : string
                18 : i32
                19 : main::Person
                20 : [3]main::Person
                21 : main::Company
                22 : main::Company
                23 : [3]main::Person
                24 : usize
                25 : main::Person
                26 : i32
                27 : main::Company
                28 : [3]main::Person
                29 : usize
                30 : main::Person
                31 : i32
                32 : i32
                33 : i32
                34 : void
                35 : () -> void
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
                2 : type
                5 : type
                9 : string
                10 : i32
                11 : main::Person
                13 : string
                14 : i32
                15 : main::Person
                17 : string
                18 : i32
                19 : main::Person
                20 : [3]main::Person
                21 : main::Company
                22 : main::Company
                23 : [3]main::Person
                24 : usize
                25 : main::Person
                26 : i32
                27 : main::Company
                28 : [3]main::Person
                29 : usize
                30 : main::Person
                31 : i32
                32 : i32
                33 : i32
                34 : void
                35 : () -> void
                l0 : main::Company
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::CannotMutate,
                    870..932,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 265..848)),
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
                2 : type
                5 : type
                8 : string
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
                2 : type
                5 : type
                8 : string
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
                    array := []i32 { 1, 2, 3 };

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
                    array :: []i32 { 1, 2, 3 };

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
                    98..113,
                    Some((TyDiagnosticHelpKind::ImmutableBinding, 49..76)),
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
                2 : [3]i32
                3 : usize
                4 : i32
                5 : {uint}
                6 : void
                7 : ([3]i32) -> void
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
                    106..126,
                    Some((TyDiagnosticHelpKind::ImmutableGlobal, 117..120)),
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
                3 : ^i32
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
                        expected: Ty::Pointer {
                            mutable: true,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
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
                foo : (arg: f32, arg2: i8) -> string : (x: i32) {
                    foo(x);
                };
            "#,
            expect![[r#"
                main::foo : (f32, i8) -> string
                6 : (f32, i8) -> string
                7 : i32
                8 : string
                9 : void
                10 : (i32) -> void
            "#]],
            |_| {
                let float = Ty::Float(32).into();
                let int = Ty::IInt(32).into();
                [
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
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: Ty::Function {
                                param_tys: vec![float, Ty::IInt(8).into()],
                                return_ty: Ty::String.into(),
                            }
                            .into(),
                            found: Ty::Function {
                                param_tys: vec![int],
                                return_ty: Ty::Void.into(),
                            }
                            .into(),
                        },
                        56..112,
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
                let int = Ty::IInt(32).into();
                [
                    (
                        TyDiagnosticKind::CalledNonFunction { found: int },
                        60..66,
                        None,
                    ),
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: int,
                            found: Ty::Function {
                                param_tys: vec![int],
                                return_ty: Ty::Void.into(),
                            }
                            .into(),
                        },
                        29..85,
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
                2 : bool
                3 : string
                4 : string
                5 : string
                6 : string
                7 : (bool) -> string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::MissingElse {
                        expected: Ty::String.into(),
                    },
                    68..130,
                    Some((
                        TyDiagnosticHelpKind::IfReturnsTypeHere {
                            found: Ty::String.into(),
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
                2 : type
                4 : string
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
                2 : type
                4 : bool
                5 : string
                6 : main::Person
                7 : void
                8 : () -> void
                l0 : main::Person
            "#]],
            |i| {
                let person_ty = Ty::Struct {
                    fqn: Some(hir::Fqn {
                        file: hir::FileName(i.intern("main.capy")),
                        name: hir::Name(i.intern("Person")),
                    }),
                    uid: 0,
                    fields: vec![
                        (hir::Name(i.intern("name")), Ty::String.into()),
                        (hir::Name(i.intern("age")), Ty::IInt(32).into()),
                    ],
                }
                .into();

                [
                    (
                        TyDiagnosticKind::Mismatch {
                            expected: Ty::String.into(),
                            found: Ty::Bool.into(),
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
                2 : type
                5 : string
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
                2 : type
                5 : string
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
                    TyDiagnosticKind::NonExistentField {
                        field: i.intern("height"),
                        found_ty: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Person")),
                            }),
                            uid: 0,
                            fields: vec![
                                (hir::Name(i.intern("name")), Ty::String.into()),
                                (hir::Name(i.intern("age")), Ty::IInt(32).into()),
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
                3 : string
                4 : string
                5 : {uint}
                6 : {uint}
                7 : <unknown>
                8 : <unknown>
                9 : (bool) -> bool
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::IfMismatch {
                        found: Ty::UInt(0).into(),
                        expected: Ty::String.into(),
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
                0 : string
                1 : string
                2 : {uint}
                3 : <unknown>
                4 : void
                5 : () -> void
                l0 : string
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
                0 : string
                1 : string
                2 : {uint}
                3 : <unknown>
                4 : void
                5 : () -> void
                l0 : string
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
                0 : string
                1 : string
                2 : <unknown>
                3 : void
                4 : () -> void
                l0 : string
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
                2 : string
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
                    my_foo : Foo = Foo {
                        a: 1,
                        b: 2,
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
                        expected: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                        found: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                    },
                    404..410,
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
                    my_foo : Foo = Foo {
                        a: 1,
                        b: 2,
                    };

                    my_bar : Bar = my_foo as Bar;
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
                    my_foo : Foo = Foo {
                        a: 1,
                        b: 2,
                    };

                    my_bar : Bar = my_foo as Bar;
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
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            fields: vec![
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                            ],
                        }
                        .into(),
                    },
                    404..417,
                    None,
                )]
            },
        );
    }

    #[test]
    fn cast_struct_diff_field_ty() {
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
                    my_foo : Foo = Foo {
                        a: 1,
                        b: 2,
                    };

                    my_bar : Bar = my_foo as Bar;
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
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(16).into()),
                            ],
                        }
                        .into(),
                    },
                    405..418,
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
                    my_foo : Foo = Foo {
                        a: 1,
                        b: 2,
                    };

                    my_bar : Bar = my_foo as Bar;
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
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            fields: vec![
                                (hir::Name(i.intern("x")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("y")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                    },
                    404..417,
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
                    c: string,
                };

                main :: () {
                    my_foo : Foo = Foo {
                        a: 1,
                        b: 2,
                    };

                    my_bar : Bar = my_foo as Bar;
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
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Foo")),
                            }),
                            uid: 0,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                            ],
                        }
                        .into(),
                        to: Ty::Struct {
                            fqn: Some(hir::Fqn {
                                file: hir::FileName(i.intern("main.capy")),
                                name: hir::Name(i.intern("Bar")),
                            }),
                            uid: 1,
                            fields: vec![
                                (hir::Name(i.intern("a")), Ty::IInt(32).into()),
                                (hir::Name(i.intern("b")), Ty::IInt(8).into()),
                                (hir::Name(i.intern("c")), Ty::String.into()),
                            ],
                        }
                        .into(),
                    },
                    435..448,
                    None,
                )]
            },
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
                3 : {uint}
                4 : {uint}
                5 : {uint}
                6 : [3]distinct'0 i32
                7 : void
                8 : () -> void
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
                1 : void
                2 : (string) -> void
                8 : void
                9 : (string) -> void
                10 : (string) -> void
                11 : (string) -> void
                12 : (string) -> void
                13 : string
                14 : void
                15 : void
                16 : () -> void
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
                5 : void
                6 : (string) -> void
                7 : <unknown>
                8 : string
                9 : <unknown>
                10 : void
                11 : () -> void
                l0 : <unknown>
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::Type.into(),
                        found: Ty::Function {
                            param_tys: vec![Ty::String.into()],
                            return_ty: Ty::Void.into(),
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
                7 : () -> void
                l0 : string
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Intern::new(Ty::String),
                        found: Intern::new(Ty::UInt(0)),
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
                4 : i32
                5 : ^i32
                8 : ^i32
                11 : ^any
                14 : ^any
                17 : ^f32
                19 : ^f32
                20 : f32
                21 : void
                22 : () -> void
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
                4 : i32
                5 : ^i32
                8 : ^i32
                11 : ^f32
                13 : ^f32
                14 : f32
                15 : void
                16 : () -> void
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
                4 : i32
                5 : ^i32
                8 : ^i32
                11 : ^any
                13 : ^any
                14 : <unknown>
                15 : void
                16 : () -> void
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
                4 : i32
                5 : ^i32
                8 : ^i32
                9 : void
                10 : () -> void
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
                4 : i32
                5 : ^i32
                8 : ^i32
                11 : ^any
                12 : void
                13 : () -> void
                l0 : i32
                l1 : ^i32
                l2 : ^any
                l3 : ^i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::IInt(32).into(),
                        }
                        .into(),
                        found: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Any.into(),
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
                    ptr := ^bytes as ^any;
                    str := ptr as string;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : u8
                2 : u8
                3 : u8
                4 : [3]u8
                5 : [3]u8
                6 : ^[3]u8
                9 : ^any
                10 : ^any
                12 : string
                13 : void
                14 : () -> void
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
                    ptr := ^bytes as ^any as ^u8;
                    str := ptr as string;
                }
            "#,
            expect![[r#"
                main::get_any : () -> void
                1 : u8
                2 : u8
                3 : u8
                4 : [3]u8
                5 : [3]u8
                6 : ^[3]u8
                9 : ^any
                12 : ^u8
                13 : ^u8
                15 : string
                16 : void
                17 : () -> void
                l0 : [3]u8
                l1 : ^u8
                l2 : string
            "#]],
            |_| [],
        );
    }

    #[test]
    fn char_ptr_to_string() {
        check(
            r"
                get_any :: () {
                    chars := [3] char { 'H', 'i', '\0' };
                    ptr := ^chars as ^any as ^char;
                    str := ptr as string;
                }
            ",
            expect![[r#"
                main::get_any : () -> void
                1 : char
                2 : char
                3 : char
                4 : [3]char
                5 : [3]char
                6 : ^[3]char
                9 : ^any
                12 : ^char
                13 : ^char
                15 : string
                16 : void
                17 : () -> void
                l0 : [3]char
                l1 : ^char
                l2 : string
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
                    my_u8 := my_char as u8;
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
                        expected: Ty::UInt(8).into(),
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
                    TyDiagnosticKind::NonExistentField {
                        field: i.intern("a"),
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
                    TyDiagnosticKind::NonExistentField {
                        field: i.intern("b"),
                        found_ty: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Pointer {
                                mutable: false,
                                sub_ty: Ty::Struct {
                                    fqn: Some(hir::Fqn {
                                        file: hir::FileName(i.intern("main.capy")),
                                        name: hir::Name(i.intern("Foo")),
                                    }),
                                    uid: 0,
                                    fields: vec![(hir::Name(i.intern("a")), Ty::IInt(32).into())],
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
                    arr := [] i32 { 1, 2, 3 };

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
                    arr := [] i32 { 1, 2, 3 };

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
                5 : {uint}
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
                    arr := [] i32 { 1, 2, 3 };

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
                                    size: 3,
                                    sub_ty: Ty::IInt(32).into(),
                                }
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    },
                    133..140,
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
                    arr := [] i32 { 1, 2, 3 };

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
                    arr :: [] i32 { 1, 2, 3 };

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
                    133..145,
                    Some((TyDiagnosticHelpKind::ImmutableRef, 105..110)),
                )]
            },
        );
    }

    #[test]
    fn entry_point_void() {
        check_with_entry(
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
        check_with_entry(
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
        check_with_entry(
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
        check_with_entry(
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
        check_with_entry(
            r#"
                foo :: (x: i32, y: bool) -> string {
                    "Hello!"
                }
            "#,
            expect![[r#"
                main::foo : (i32, bool) -> string
                3 : string
                4 : string
                5 : (i32, bool) -> string
            "#]],
            |_| {
                [
                    (TyDiagnosticKind::EntryHasParams, 24..41, None),
                    (TyDiagnosticKind::EntryBadReturn, 45..51, None),
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

                    arr : imaginary_vec3 = [] imaginary { 1, 2, 3 };

                    arr[0] as i32
                }
            "#,
            expect![[r#"
                main::main : () -> i32
                1 : type
                3 : type
                6 : type
                9 : {uint}
                10 : {uint}
                11 : {uint}
                12 : distinct'1 [3]distinct'0 i32
                13 : distinct'1 [3]distinct'0 i32
                14 : usize
                15 : distinct'0 i32
                17 : i32
                18 : i32
                19 : () -> i32
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

                    my_complex := complex {
                        real_part: 5,
                        imaginary_part: 42,
                    };

                    my_complex.real_part as i32 + my_complex.imaginary_part as i32
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
                
                    my_complex := complex {
                        real_part: 5,
                        imaginary_part: 42,
                    };
                
                    do_math :: (c: complex) -> imaginary_vec3 {
                        // this is kind of akward because while we can access locals
                        // in the parameters and return type, we can't access `imaginary`
                        // from inside the body of this lambda
                        // this could be alleviated by adding a `type_of` builtin
                        [3] i32 { 1, c.real_part * c.imaginary_part as i32, 3 }
                    };
                
                    do_math(my_complex)[1] as i32
                }
            "#,
            expect![[r#"
                main::main : () -> i32
                1 : type
                3 : type
                6 : type
                9 : type
                11 : i32
                12 : distinct'0 i32
                13 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                17 : i32
                18 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                19 : i32
                20 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                21 : distinct'0 i32
                23 : i32
                24 : i32
                25 : i32
                26 : [3]i32
                27 : [3]i32
                28 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
                29 : (struct'2 {real_part: i32, imaginary_part: distinct'0 i32}) -> distinct'1 [3]distinct'0 i32
                30 : struct'2 {real_part: i32, imaginary_part: distinct'0 i32}
                31 : distinct'1 [3]distinct'0 i32
                32 : usize
                33 : distinct'0 i32
                35 : i32
                36 : i32
                37 : () -> i32
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
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : void
                2 : void
                3 : () -> void
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
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : {uint}
                1 : void
                2 : void
                3 : void
                4 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::Void.into(),
                        found: Ty::UInt(0).into(),
                    },
                    81..84,
                    None,
                )]
            },
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
                        expected: Ty::Void.into(),
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
                    `blk {
                        {
                            break blk` {};
                        }

                        42
                    }               
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
                1 : void
                2 : {uint}
                3 : <unknown>
                4 : <unknown>
                5 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::Void.into(),
                        found: Ty::UInt(0).into(),
                    },
                    176..178,
                    Some((
                        TyDiagnosticHelpKind::BreakHere {
                            break_ty: Ty::Void.into(),
                        },
                        110..124,
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
                    break blk` 42;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                1 : void
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
                1 : string
                2 : {uint}
                3 : <unknown>
                4 : () -> i32
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::String.into(),
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
    fn break_from_loop() {
        check(
            r#"
                foo :: () {
                    `my_loop loop {
                        break my_loop`;
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                0 : void
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
                    `my_loop loop {
                        break my_loop` 42;
                    }
                }
            "#,
            expect![[r#"
                main::foo : () -> i32
                1 : i32
                2 : void
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn break_from_while() {
        check(
            r#"
                foo :: () {
                    `my_loop while 2 + 2 == 4 {
                        break my_loop`;
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
                    `my_loop while 2 + 2 == 4 {
                        break my_loop` {};
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
                6 : void
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
                    `my_loop while 2 + 2 == 4 {
                        break my_loop` 42;
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
                6 : void
                7 : void
                8 : void
                9 : () -> void
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::Void.into(),
                        found: Ty::UInt(0).into(),
                    },
                    116..118,
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
                1 : void
                2 : void
                3 : i32
                4 : i32
                5 : () -> i32
            "#]],
            |_| [],
        )
    }

    #[test]
    fn implicit_weak_ptr_to_any() {
        check(
            r#"
                foo :: () {
                    x : ^any = ^42;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : {uint}
                3 : ^{uint}
                4 : void
                5 : () -> void
                l0 : ^any
            "#]],
            |_| {
                [(
                    TyDiagnosticKind::Mismatch {
                        expected: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::Any.into(),
                        }
                        .into(),
                        found: Ty::Pointer {
                            mutable: false,
                            sub_ty: Ty::UInt(0).into(),
                        }
                        .into(),
                    },
                    60..63,
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
                    x : ^any = ^42 as ^i32;
                }
            "#,
            expect![[r#"
                main::foo : () -> void
                2 : i32
                3 : ^i32
                6 : ^i32
                7 : void
                8 : () -> void
                l0 : ^any
            "#]],
            |_| [],
        )
    }
}

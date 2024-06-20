use std::collections::HashSet;

use hir::{Descendant, Expr, FQComptime, FQLambda, LocalDef, ScopeId, Stmt};
use indexmap::IndexMap;
use interner::Interner;
use internment::Intern;
use itertools::Itertools;
use la_arena::{ArenaMap, Idx};
use rustc_hash::{FxHashMap, FxHashSet};
use text_size::TextRange;
use topo::TopoSort;

use crate::{
    ty::BinaryOutput, ComptimeResult, EvalComptimeFn, InferResult, Inferrable, ProjectInference,
    Ty, TyDiagnostic, TyDiagnosticHelp, TyDiagnosticHelpKind, TyDiagnosticKind, TypedOp,
    UnaryOutput,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprIsConst {
    Const,
    Runtime,
    /// the same as `Runtime` but doesn't report an error since there's missing information
    Unknown,
}

impl ExprIsConst {
    fn should_report_not_const(self) -> bool {
        matches!(self, ExprIsConst::Runtime)
    }

    fn is_const(self) -> bool {
        matches!(self, ExprIsConst::Const)
    }
}

enum ExprMutability {
    Mutable,
    ImmutableBinding(TextRange),
    NotMutatingRefThroughDeref(TextRange),
    ImmutableRef(TextRange),
    ImmutableParam(TextRange, bool),
    ImmutableGlobal(TextRange),
    CannotMutate(TextRange),
}

impl ExprMutability {
    fn into_diagnostic(self) -> Option<TyDiagnosticHelp> {
        match self {
            ExprMutability::CannotMutate(range) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::FoundToBeImmutable,
                range,
            }),
            ExprMutability::ImmutableBinding(range) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::ImmutableBinding,
                range,
            }),
            ExprMutability::ImmutableRef(range) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::ImmutableRef,
                range,
            }),
            ExprMutability::ImmutableParam(range, assignment) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::ImmutableParam { assignment },
                range,
            }),
            ExprMutability::ImmutableGlobal(range) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::ImmutableGlobal,
                range,
            }),
            ExprMutability::NotMutatingRefThroughDeref(range) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::NotMutatingRefThroughDeref,
                range,
            }),
            _ => None,
        }
    }
}

pub(crate) struct GlobalInferenceCtx<'a> {
    pub(crate) file: hir::FileName,
    pub(crate) current_inferring: Inferrable,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) world_bodies: &'a hir::WorldBodies,
    pub(crate) bodies: &'a hir::Bodies,
    pub(crate) interner: &'a Interner,
    // todo: what happens to this when an uninferred global is reached?
    // should this be stored in `InferenceCtx`?
    pub(crate) local_usages: ArenaMap<Idx<hir::LocalDef>, FxHashSet<Idx<hir::Stmt>>>,
    pub(crate) inferred_stmts: &'a mut FxHashSet<(hir::FileName, Idx<hir::Stmt>)>,
    pub(crate) tys: &'a mut ProjectInference,
    pub(crate) param_tys: Vec<Intern<Ty>>,
    pub(crate) all_inferred: &'a FxHashSet<Inferrable>,
    pub(crate) to_infer: &'a mut TopoSort<Inferrable>,
    pub(crate) diagnostics: &'a mut Vec<TyDiagnostic>,
    pub(crate) eval_comptime: &'a mut dyn EvalComptimeFn,
}

impl GlobalInferenceCtx<'_> {
    pub(crate) fn finish_body(
        &mut self,
        body: Idx<Expr>,
        expected_ty: Option<Intern<Ty>>,
        global: bool,
    ) -> InferResult<Intern<Ty>> {
        self.infer_expr(body)?;

        for (def, usages) in self.local_usages.clone().iter() {
            self.local_usages.get_mut(def).unwrap().clear();

            self.reinfer_usages(usages.clone());
        }

        let mut actual_ty = self.reinfer_expr(body);

        // {int} globals -> i32
        let i32 = Ty::IInt(32).into();
        // {float} gloabls -> f64
        let f64 = Ty::Float(64).into();

        if let Some(expected_ty) = expected_ty {
            self.expect_match(actual_ty, expected_ty, body);
            self.replace_weak_tys(body, expected_ty);

            actual_ty = expected_ty;
        } else if global && self.replace_weak_tys(body, i32) {
            actual_ty = i32;
        } else if global && self.replace_weak_tys(body, f64) {
            actual_ty = f64;
        }

        if global && self.get_const(body).should_report_not_const() {
            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::GlobalNotConst,
                file: self.file,
                range: self.bodies.range_for_expr(body),
                expr: Some(body),
                help: None,
            });

            // println!("not const: {:#?}", &self.bodies[body]);
        }

        Ok(actual_ty)
    }

    fn reinfer_usages(&mut self, usages: FxHashSet<Idx<hir::Stmt>>) {
        for usage in usages {
            match self.bodies[usage] {
                hir::Stmt::LocalDef(user_local_def) => {
                    let user_local_body = &self.bodies[user_local_def];

                    if let Some(value) = user_local_body.value {
                        let user_local_ty = self.reinfer_expr(value);

                        // if there is no type annotation on the user, then replace it's type
                        if user_local_body.ty.is_none() {
                            self.tys[self.file]
                                .local_tys
                                .insert(user_local_def, user_local_ty);
                        }
                    }
                }
                hir::Stmt::Assign(assign) => {
                    let assign_body = &self.bodies[assign];

                    self.reinfer_expr(assign_body.dest);
                    self.reinfer_expr(assign_body.value);
                }
                hir::Stmt::Expr(expr) => {
                    self.reinfer_expr(expr);
                }
                hir::Stmt::Break { value, .. } => {
                    if let Some(value) = value {
                        self.reinfer_expr(value);
                    }
                }
                hir::Stmt::Defer { expr, .. } => {
                    self.reinfer_expr(expr);
                }
                hir::Stmt::Continue { .. } => {}
            }
        }
    }

    /// recursively replaces weakly-typed expressions with strong types.
    ///
    /// ```text
    /// x := 42;        // x is of type {uint}, which is a weak type
    /// y : u16 = x;    // x's type is changed to be u16 instead of {uint}
    /// ```
    ///
    /// This also has to account for usages of local variables
    ///
    /// ```text
    /// x := 42;            // x is a weak {uint}
    /// if x > 10 { ... }   // the type of x here is {uint}
    /// y : u16 = x;        // not only is x's type changed, but the above if condition is changed
    /// ```
    ///
    /// returns true if `expr` had a weak type, returns false if `expr` had a strong type
    fn replace_weak_tys(&mut self, expr: Idx<hir::Expr>, new_ty: Intern<Ty>) -> bool {
        let expr_body = &self.bodies[expr];
        if matches!(expr_body, Expr::Missing) {
            return false;
        }

        let found_ty = self.tys[self.file].expr_tys[expr];
        if !found_ty.is_weak_replaceable_by(&new_ty) {
            return false;
        }

        let expr_body = expr_body.clone();

        self.tys[self.file].expr_tys.insert(expr, new_ty);

        match expr_body {
            Expr::IntLiteral(num) => {
                if let Some(max_size) = new_ty.get_max_int_size() {
                    if num > max_size {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IntTooBigForType {
                                found: num,
                                max: max_size,
                                ty: new_ty,
                            },
                            file: self.file,
                            expr: Some(expr),
                            range: self.bodies.range_for_expr(expr),
                            help: None,
                        });
                    }
                }
            }
            Expr::ArrayLiteral { ty: None, items } => {
                let (_, sub_ty) = new_ty.as_array().unwrap();

                for item in items {
                    self.replace_weak_tys(item, sub_ty);
                }
            }
            Expr::Paren(Some(expr)) => {
                self.replace_weak_tys(expr, new_ty);
            }
            Expr::Block { tail_expr, .. } => {
                if let Some(scope_id) = self.bodies.block_to_scope_id(expr) {
                    for usage in self.bodies.scope_id_usages(scope_id) {
                        if let hir::Stmt::Break {
                            value: Some(value), ..
                        } = self.bodies[*usage]
                        {
                            self.replace_weak_tys(value, new_ty);
                        }
                    }
                }

                if let Some(tail_expr) = tail_expr {
                    self.replace_weak_tys(tail_expr, new_ty);
                }
            }
            Expr::If {
                body, else_branch, ..
            } => {
                self.replace_weak_tys(body, new_ty);
                if let Some(else_branch) = else_branch {
                    self.replace_weak_tys(else_branch, new_ty);
                }
            }
            Expr::While {
                condition: None, ..
            } => {
                if let Some(scope_id) = self.bodies.block_to_scope_id(expr) {
                    for usage in self.bodies.scope_id_usages(scope_id) {
                        if let hir::Stmt::Break {
                            value: Some(value), ..
                        } = self.bodies[*usage]
                        {
                            self.replace_weak_tys(value, new_ty);
                        }
                    }
                }
            }
            Expr::Comptime(comptime) => {
                let body = self.bodies[comptime].body;

                self.replace_weak_tys(body, new_ty);
            }
            Expr::Deref { pointer } => {
                let mutable = self.tys[self.file].expr_tys[expr]
                    .as_pointer()
                    .map(|(mutable, _)| mutable)
                    .unwrap_or_default();

                self.replace_weak_tys(
                    pointer,
                    Ty::Pointer {
                        mutable,
                        sub_ty: new_ty,
                    }
                    .into(),
                );
            }
            Expr::Ref { expr: inner, .. } => {
                // `^mut {uint}` is technically replaceable by `^i32`, but we still want to
                // maintain the mutablility.
                let old_mutable = found_ty.as_pointer().unwrap().0;

                let sub_ty = new_ty.as_pointer().unwrap().1;

                self.replace_weak_tys(inner, sub_ty);

                self.tys[self.file].expr_tys.insert(
                    expr,
                    Ty::Pointer {
                        mutable: old_mutable,
                        sub_ty,
                    }
                    .into(),
                );
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.replace_weak_tys(lhs, new_ty);
                self.replace_weak_tys(rhs, new_ty);
            }
            Expr::Unary { expr, .. } => {
                self.replace_weak_tys(expr, new_ty);
            }
            Expr::Local(local_def) => {
                let local_body = &self.bodies[local_def];

                if let Some(value) = local_body.value {
                    if self.replace_weak_tys(value, new_ty) {
                        self.tys[self.file].local_tys.insert(local_def, new_ty);
                    }
                }

                // now get everything that used this variable and make sure the types are correct for those things
                let usages = self
                    .local_usages
                    .get(local_def)
                    .cloned()
                    .unwrap_or_default();

                // now that we have the usages, clear them so no nasty recursion takes place
                if let Some(usages) = self.local_usages.get_mut(local_def) {
                    usages.clear();
                }

                self.reinfer_usages(usages);

                // self.reinfer_expr(self.bodies[local_def].value);
            }
            Expr::StructLiteral { members, .. } => {
                let member_tys: FxHashMap<_, _> =
                    new_ty.as_struct().unwrap().iter().copied().collect();

                for (name, value) in members.into_iter() {
                    let Some(name) = name else { continue };
                    let new_member_ty = member_tys[&name.name];

                    self.replace_weak_tys(value, new_member_ty);
                }
            }
            _ => {}
        }

        true
    }

    fn get_const(&self, expr: Idx<Expr>) -> ExprIsConst {
        let mut to_check = vec![(self.file, expr)];

        let mut idx = 0;
        while let Some((file, expr)) = to_check.get(idx).copied() {
            let result = match &self.world_bodies[file][expr] {
                Expr::Missing
                | Expr::Lambda(_)
                | Expr::Import(_)
                | Expr::PrimitiveTy { .. }
                | Expr::StructDecl { .. }
                | Expr::Distinct { .. }
                | Expr::Comptime(_)
                | Expr::StringLiteral(_)
                | Expr::IntLiteral(_)
                | Expr::FloatLiteral(_)
                | Expr::BoolLiteral(_) => ExprIsConst::Const,
                Expr::ArrayLiteral { items, .. } if self.tys[file][expr].is_array() => {
                    to_check.extend(items.iter().map(|e| (file, *e)));
                    ExprIsConst::Const
                }
                Expr::LocalGlobal(global) => {
                    let fqn = hir::Fqn {
                        file,
                        name: global.name,
                    };

                    if self.world_bodies.is_extern(fqn) {
                        ExprIsConst::Runtime
                    } else {
                        let inferrable = Inferrable::Global(fqn);
                        if !self.all_inferred.contains(&inferrable) {
                            // this can only happen if there's been a cyclic error
                            assert_eq!(*self.tys[fqn].0, Ty::NotYetResolved);
                            return ExprIsConst::Unknown;
                        }

                        to_check.push((file, self.world_bodies.body(fqn)));
                        ExprIsConst::Const
                    }
                }
                Expr::Local(local) => {
                    let local_def = &self.world_bodies[file][*local];

                    if let Some(value) = local_def.value {
                        to_check.push((file, value));
                    }

                    if local_def.mutable {
                        ExprIsConst::Runtime
                    } else if local_def.value.is_none() {
                        // this protects against cases like `x ::;`
                        ExprIsConst::Unknown
                    } else {
                        ExprIsConst::Const
                    }
                }
                Expr::Member { previous, field } => {
                    let old_file = file;

                    if let Ty::File(file) = self.tys[old_file][*previous].as_ref() {
                        to_check.push((old_file, *previous));

                        let fqn = hir::Fqn {
                            file: *file,
                            name: field.name,
                        };

                        if !self.world_bodies.exists(fqn) {
                            ExprIsConst::Unknown
                        } else if self.world_bodies.is_extern(fqn) {
                            ExprIsConst::Runtime
                        } else {
                            let inferrable = Inferrable::Global(fqn);
                            if !self.all_inferred.contains(&inferrable) {
                                // this can only happen if there's been a cyclic error
                                assert_eq!(*self.tys[fqn].0, Ty::NotYetResolved);
                                return ExprIsConst::Unknown;
                            }

                            to_check.push((*file, self.world_bodies.body(fqn)));
                            ExprIsConst::Const
                        }
                    } else {
                        ExprIsConst::Runtime
                    }
                }
                _ => {
                    if matches!(*(self.tys[file][expr]), Ty::Type | Ty::File(_)) {
                        ExprIsConst::Const
                    } else {
                        ExprIsConst::Runtime
                    }
                }
            };

            if result == ExprIsConst::Runtime || result == ExprIsConst::Unknown {
                return result;
            }

            idx += 1;
        }

        ExprIsConst::Const
    }

    /// `deref` allows certain expressions to be mutable
    /// only if they are being mutated through a deref
    fn get_mutability(&self, expr: Idx<Expr>, assignment: bool, deref: bool) -> ExprMutability {
        match &self.bodies[expr] {
            Expr::Missing => ExprMutability::Mutable,
            Expr::ArrayLiteral { .. } => ExprMutability::Mutable,
            Expr::StructLiteral { .. } => ExprMutability::Mutable,
            Expr::Ref { mutable, .. } => match (*mutable, deref) {
                (true, _) => ExprMutability::Mutable,
                // (true, false) => ExprMutability::NotMutatingRefThroughDeref(
                //     self.bodies.range_for_expr(expr),
                // ),
                _ => ExprMutability::ImmutableRef(self.bodies.range_for_expr(expr)),
            },
            Expr::Deref { pointer } => self.get_mutability(*pointer, assignment, true),
            Expr::Index { source: array, .. } => self.get_mutability(
                *array,
                assignment,
                deref || self.tys[self.file][*array].is_pointer(),
            ),
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => self.get_mutability(*tail_expr, assignment, deref),
            Expr::Local(local_def) if deref => {
                let local_def = &self.bodies[*local_def];

                if let Some(value) = local_def.value {
                    self.get_mutability(value, false, deref)
                } else {
                    // todo: does this make sense?
                    ExprMutability::Mutable
                }
            }
            Expr::Local(local_def) if !deref => {
                let local_def = &self.bodies[*local_def];

                if local_def.mutable {
                    ExprMutability::Mutable
                } else {
                    ExprMutability::ImmutableBinding(local_def.range)
                }
            }
            Expr::Param { idx, range } => {
                let param_ty = self.param_tys[*idx as usize];

                match param_ty.as_pointer() {
                    Some((mutable, _)) if deref => {
                        if mutable {
                            ExprMutability::Mutable
                        } else {
                            // todo: change this to be the range of the param's type
                            ExprMutability::ImmutableRef(*range)
                        }
                    }
                    Some((mutable, _)) if assignment => {
                        if mutable {
                            ExprMutability::NotMutatingRefThroughDeref(
                                self.bodies.range_for_expr(expr),
                            )
                        } else {
                            ExprMutability::ImmutableRef(*range)
                        }
                    }
                    _ => ExprMutability::ImmutableParam(*range, assignment),
                }
            }
            Expr::LocalGlobal(name) => {
                let fqn = hir::Fqn {
                    file: self.file,
                    name: name.name,
                };

                ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
            }
            Expr::Member { previous, field } => {
                let previous_ty = self.tys[self.file][*previous];
                match previous_ty.as_ref() {
                    Ty::File(file) => {
                        let fqn = hir::Fqn {
                            file: *file,
                            name: field.name,
                        };

                        if *file == self.file {
                            ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
                        } else {
                            ExprMutability::ImmutableGlobal(field.range)
                        }
                    }
                    _ if deref => {
                        let path_ty = &self.tys[self.file][expr];

                        if path_ty
                            .as_pointer()
                            .map(|(mutable, _)| mutable)
                            .unwrap_or(true)
                        {
                            ExprMutability::Mutable
                        } else {
                            // todo: use the actual range of the struct literal, not the range of this field name
                            ExprMutability::ImmutableRef(field.range)
                        }
                    }
                    _ => self.get_mutability(
                        *previous,
                        assignment,
                        deref || previous_ty.is_pointer(),
                    ),
                }
            }
            Expr::Call { .. } if deref => ExprMutability::Mutable,
            Expr::Cast { .. } if deref => {
                let ty = self.tys[self.file][expr];

                match ty.as_pointer() {
                    Some((mutable, _)) if deref => {
                        if mutable {
                            ExprMutability::Mutable
                        } else {
                            // todo: change this to be the range of the param's type
                            ExprMutability::ImmutableRef(self.bodies.range_for_expr(expr))
                        }
                    }
                    Some((mutable, _)) if assignment => {
                        if mutable {
                            ExprMutability::NotMutatingRefThroughDeref(
                                self.bodies.range_for_expr(expr),
                            )
                        } else {
                            ExprMutability::ImmutableRef(self.bodies.range_for_expr(expr))
                        }
                    }
                    _ => ExprMutability::CannotMutate(self.bodies.range_for_expr(expr)),
                }
            }
            Expr::Paren(Some(expr)) => self.get_mutability(*expr, assignment, deref),
            _ => ExprMutability::CannotMutate(self.bodies.range_for_expr(expr)),
        }
    }

    fn find_usages(&mut self, exprs: &[Idx<hir::Expr>], local_usage: Idx<hir::Stmt>) {
        let mut locals = HashSet::default();
        for expr in exprs {
            self.get_referenced_locals(*expr, &mut locals);
        }

        for local in locals {
            if let Some(usages) = self.local_usages.get_mut(local) {
                usages.insert(local_usage);
            } else {
                let mut usages = FxHashSet::default();
                usages.insert(local_usage);

                self.local_usages.insert(local, usages);
            }
        }
    }

    fn get_referenced_locals(&self, expr: Idx<hir::Expr>, locals: &mut FxHashSet<Idx<LocalDef>>) {
        locals.extend(
            self.bodies
                .descendants(expr, hir::DescentOpts::Reinfer)
                .filter_map(|desc| match desc {
                    Descendant::Expr(expr) => match self.bodies[expr] {
                        Expr::Local(local) => Some(local),
                        _ => None,
                    },
                    Descendant::Stmt(_) => None,
                }),
        );
    }

    fn reinfer_expr(&mut self, expr: Idx<hir::Expr>) -> Intern<Ty> {
        let previous_ty = self.tys[self.file][expr];
        if *previous_ty == Ty::Unknown {
            return previous_ty;
        }

        fn all_usages_ty(ctx: &mut GlobalInferenceCtx, label_id: ScopeId) -> Intern<Ty> {
            let usages = ctx.bodies.scope_id_usages(label_id);

            let mut max_ty: Option<Intern<Ty>> = None;
            for usage in usages.iter() {
                let ty = match ctx.bodies[*usage] {
                    hir::Stmt::Break {
                        value: Some(value), ..
                    } => ctx.tys[ctx.file][value],
                    hir::Stmt::Break { value: None, .. } => Ty::Void.into(),
                    _ => continue,
                };

                if let Some(max) = max_ty {
                    max_ty = max.max(&ty).map(|ty| ty.into());
                } else {
                    max_ty = Some(ty);
                }
            }

            max_ty.unwrap_or_else(|| Ty::Void.into())
        }

        for next in self
            .bodies
            .descendants(expr, hir::DescentOpts::Eval)
            .collect_vec()
            .into_iter()
            .rev()
        {
            match next {
                Descendant::Expr(expr) => {
                    let previous_ty = self.tys[self.file][expr];

                    if *previous_ty == Ty::Unknown || *previous_ty == Ty::NoEval {
                        continue;
                    }

                    let new_ty = match &self.bodies[expr] {
                        Expr::IntLiteral(num) => match *previous_ty {
                            Ty::IInt(0) if *num > i32::MAX as u64 => Ty::IInt(64).into(),
                            Ty::UInt(0) if *num > u32::MAX as u64 => Ty::UInt(64).into(),
                            _ => continue,
                        },
                        Expr::Ref {
                            mutable,
                            expr: inner,
                        } => {
                            let inner_ty = self.tys[self.file][*inner];

                            if *inner_ty == Ty::Type {
                                inner_ty
                            } else {
                                Ty::Pointer {
                                    mutable: *mutable,
                                    sub_ty: inner_ty,
                                }
                                .into()
                            }
                        }
                        Expr::Deref { pointer } => {
                            let inner_ty = self.tys[self.file][*pointer];

                            inner_ty
                                .as_pointer()
                                .map(|(_, sub_ty)| sub_ty)
                                .unwrap_or_else(|| Ty::Unknown.into())
                        }
                        Expr::Binary { lhs, rhs, op } => {
                            let lhs_ty = self.tys[self.file][*lhs];
                            let rhs_ty = self.tys[self.file][*rhs];

                            if let Some(output_ty) = op.get_possible_output_ty(&lhs_ty, &rhs_ty) {
                                let max_ty = output_ty.max_ty.into();
                                self.replace_weak_tys(*lhs, max_ty);
                                self.replace_weak_tys(*rhs, max_ty);

                                output_ty.final_output_ty.into()
                            } else {
                                op.default_ty().into()
                            }
                        }
                        Expr::Unary { expr: inner, op } => {
                            let inner_ty = self.tys[self.file][*inner];
                            if op.can_perform(&inner_ty) {
                                op.get_possible_output_ty(inner_ty)
                            } else {
                                op.default_ty().into()
                            }
                        }
                        Expr::Index { source, .. } => {
                            let mut source_ty = self.tys[self.file][*source];

                            while let Some(ptr) = source_ty.as_pointer() {
                                source_ty = ptr.1;
                            }

                            source_ty
                                .as_array()
                                .map(|(_, sub_ty)| sub_ty)
                                .or_else(|| source_ty.as_slice())
                                .unwrap_or_else(|| Ty::Unknown.into())
                        }
                        Expr::Block { tail_expr, .. } => {
                            let tail_ty = tail_expr.map(|tail_expr| self.tys[self.file][tail_expr]);

                            if let Some(label_id) = self.bodies.block_to_scope_id(expr) {
                                let usages_ty = all_usages_ty(self, label_id);

                                if let Some(new_tail) = tail_ty {
                                    usages_ty.max(&new_tail).unwrap_or(Ty::Unknown).into()
                                } else {
                                    usages_ty
                                }
                            } else {
                                tail_ty.unwrap_or_else(|| Ty::Void.into())
                            }
                        }
                        Expr::If {
                            body, else_branch, ..
                        } => {
                            let body_ty = self.tys[self.file][*body];

                            if let Some(else_branch) = else_branch {
                                let new_else = self.tys[self.file][*else_branch];

                                body_ty.max(&new_else).unwrap_or(Ty::Unknown).into()
                            } else if *body_ty == Ty::NoEval {
                                Ty::Void.into()
                            } else {
                                body_ty
                            }
                        }
                        Expr::While { condition, .. } => {
                            if condition.is_some() {
                                Ty::Void.into()
                            } else if let Some(label_id) = self.bodies.block_to_scope_id(expr) {
                                all_usages_ty(self, label_id)
                            } else {
                                Ty::Void.into()
                            }
                        }
                        Expr::Local(local) => self.tys[self.file].local_tys[*local],
                        _ => continue,
                    };

                    let loss_of_distinct = matches!(previous_ty.as_ref(), Ty::Distinct { .. })
                        && new_ty.is_functionally_equivalent_to(&previous_ty, false);

                    #[cfg(debug_assertions)]
                    if previous_ty != new_ty
                        && !(previous_ty.is_weak_replaceable_by(&new_ty) || loss_of_distinct)
                    {
                        panic!(
                            "#{} : {:?} is not weak replaceable by {:?}",
                            expr.into_raw(),
                            previous_ty,
                            new_ty
                        );
                    }

                    if !loss_of_distinct {
                        self.tys[self.file].expr_tys.insert(expr, new_ty);
                    }
                }
                Descendant::Stmt(stmt) => match &self.bodies[stmt] {
                    Stmt::Expr(_) => {}
                    Stmt::LocalDef(local_def) => {
                        let def_body = &self.bodies[*local_def];

                        if def_body.ty.is_some() {
                            // if there's a type annotation, then even if the value changed
                            // types, the local will always have the type of it's type annotation
                            continue;
                        }

                        let Some(value) = def_body.value else {
                            continue;
                        };

                        let previous_ty = self.tys[self.file][*local_def];
                        let new_ty = self.tys[self.file][value];

                        let loss_of_distinct = matches!(previous_ty.as_ref(), Ty::Distinct { .. })
                            && new_ty.is_functionally_equivalent_to(&previous_ty, false);

                        #[cfg(debug_assertions)]
                        if previous_ty != new_ty
                            && !(previous_ty.is_weak_replaceable_by(&new_ty) || loss_of_distinct)
                        {
                            panic!(
                                "#{} : {:?} is not weak replaceable by {:?}",
                                expr.into_raw(),
                                previous_ty,
                                new_ty
                            );
                        }

                        if !loss_of_distinct {
                            self.tys[self.file].local_tys.insert(*local_def, new_ty);
                        }
                    }
                    Stmt::Assign(_) => {}
                    Stmt::Break { .. } => {}
                    Stmt::Continue { .. } => {}
                    Stmt::Defer { .. } => {}
                },
            }
        }

        self.tys[self.file][expr]
    }

    // This function is indent hell but it's worth it to make it stack overflow free
    fn infer_expr(&mut self, expr: Idx<Expr>) -> InferResult<Intern<Ty>> {
        if let (Some(ty), None) = (
            self.tys[self.file].expr_tys.get(expr),
            self.bodies.block_to_scope_id(expr),
        ) {
            return Ok(*ty);
        }

        let descendants = self.bodies.descendants(expr, hir::DescentOpts::Eval);

        // This all works because children will ALWAYS come before parents
        for descendant in descendants.collect_vec().into_iter().rev() {
            match descendant {
                Descendant::Expr(expr) => {
                    if self.tys[self.file].expr_tys.contains_idx(expr)
                        && self.bodies.block_to_scope_id(expr).is_none()
                    {
                        continue;
                    }

                    let ty = match &self.bodies[expr] {
                        Expr::Missing => Ty::Unknown.into(),
                        Expr::IntLiteral(_) => Ty::UInt(0).into(),
                        Expr::FloatLiteral(_) => Ty::Float(0).into(),
                        Expr::BoolLiteral(_) => Ty::Bool.into(),
                        Expr::StringLiteral(_) => Ty::String.into(),
                        Expr::CharLiteral(_) => Ty::Char.into(),
                        Expr::ArrayDecl { .. } => {
                            self.const_ty(expr)?;
                            Ty::Type.into()
                        }
                        Expr::ArrayLiteral {
                            ty: Some(ty),
                            items,
                        } => {
                            let sub_ty = self.const_ty(*ty)?;
                            for item in items {
                                let item_ty = self.tys[self.file][*item];
                                self.expect_match(item_ty, sub_ty, *item);
                            }

                            Ty::Array {
                                anonymous: false,
                                size: items.len() as u64,
                                sub_ty,
                            }
                            .into()
                        }
                        Expr::ArrayLiteral { ty: None, items } => {
                            // todo: allow `.[ .. ]` to cast to `[]core.Any`
                            let mut max_ty = None;
                            let mut any_error = false;
                            for item in items {
                                let item_ty = self.tys[self.file][*item];

                                match max_ty {
                                    None => max_ty = Some(item_ty),
                                    Some(previous) => {
                                        if !any_error {
                                            max_ty = Some(
                                                previous
                                                    .max(&item_ty)
                                                    .unwrap_or_else(|| {
                                                        if !any_error {
                                                            self.diagnostics.push(TyDiagnostic {
                                                                kind: TyDiagnosticKind::Mismatch {
                                                                    expected: previous,
                                                                    found: item_ty,
                                                                },
                                                                file: self.file,
                                                                expr: Some(*item),
                                                                range: self
                                                                    .bodies
                                                                    .range_for_expr(*item),
                                                                help: None,
                                                            });
                                                            any_error = true;
                                                        }
                                                        Ty::Unknown
                                                    })
                                                    .into(),
                                            )
                                        }
                                    }
                                }
                            }

                            if let Some(max_ty) = max_ty.filter(|_| !any_error) {
                                for item in items {
                                    self.replace_weak_tys(*item, max_ty);
                                }
                            }

                            let sub_ty = if any_error {
                                Ty::Unknown.into()
                            } else {
                                // todo: instead of void, create a new type that casts to anything
                                max_ty.unwrap_or_else(|| Ty::Void.into())
                            };

                            Ty::Array {
                                anonymous: true,
                                size: items.len() as u64,
                                sub_ty,
                            }
                            .into()
                        }
                        Expr::Index { source, index } => {
                            let source_ty = self.tys[self.file][*source];
                            // because it's annoying to do `foo^[0]`, this code lets you do `foo[0]`
                            let mut deref_source_ty = source_ty;
                            while let Some((_, sub_ty)) = deref_source_ty.as_pointer() {
                                deref_source_ty = sub_ty;
                            }

                            let index_ty = self.tys[self.file][*index];

                            if self.expect_match(index_ty, Ty::UInt(u8::MAX).into(), *index) {
                                self.replace_weak_tys(*index, Ty::UInt(u8::MAX).into());
                            }

                            if *deref_source_ty == Ty::Unknown {
                                Ty::Unknown.into()
                            } else if let Some((actual_size, array_sub_ty)) =
                                deref_source_ty.as_array()
                            {
                                if let hir::Expr::IntLiteral(index) = self.bodies[*index] {
                                    if index >= actual_size {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::IndexOutOfBounds {
                                                index,
                                                actual_size,
                                                array_ty: source_ty,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help: None,
                                        });
                                    }
                                }

                                if array_sub_ty.is_any_type() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::IndexAny {
                                            size: Some(actual_size),
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                } else {
                                    array_sub_ty
                                }
                            } else if let Some(slice_sub_ty) = deref_source_ty.as_slice() {
                                if slice_sub_ty.is_any_type() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::IndexAny { size: None },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                } else {
                                    slice_sub_ty
                                }
                            } else {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::IndexNonArray { found: source_ty },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            }
                        }
                        Expr::Cast { expr: sub_expr, ty } => {
                            let expr_ty = self.tys[self.file][*sub_expr];

                            if *expr_ty == Ty::Unknown {
                                Ty::Unknown.into()
                            } else {
                                let cast_ty = self.const_ty(*ty)?;

                                if cast_ty.is_unknown() {
                                    Ty::Unknown.into()
                                } else {
                                    if !expr_ty.can_cast_to(&cast_ty) {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::Uncastable {
                                                from: expr_ty,
                                                to: cast_ty,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help: None,
                                        });
                                    }

                                    // replacing the existing type with the casted type
                                    self.replace_weak_tys(*sub_expr, cast_ty);

                                    cast_ty
                                }
                            }
                        }
                        Expr::Ref {
                            mutable,
                            expr: inner,
                        } => {
                            let inner_ty = self.tys[self.file][*inner];

                            if *inner_ty == Ty::Type {
                                self.const_ty(expr)?;
                                inner_ty
                            } else {
                                if *mutable {
                                    let help =
                                        self.get_mutability(*inner, false, false).into_diagnostic();

                                    if help.is_some() {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::MutableRefToImmutableData,
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help,
                                        })
                                    }
                                }

                                Ty::Pointer {
                                    mutable: *mutable,
                                    sub_ty: inner_ty,
                                }
                                .into()
                            }
                        }
                        Expr::Deref { pointer } => {
                            let deref_ty = self.tys[self.file][*pointer];

                            match *deref_ty {
                                Ty::Pointer { sub_ty, .. } if *sub_ty == Ty::Any => {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::DerefAny,
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                }
                                Ty::Pointer { sub_ty, .. } => sub_ty,
                                _ => {
                                    if !deref_ty.is_unknown() {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::DerefNonPointer {
                                                found: deref_ty,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help: None,
                                        });
                                    }

                                    Ty::Unknown.into()
                                }
                            }
                        }
                        Expr::Binary { lhs, rhs, op } => {
                            let lhs_ty = self.tys[self.file][*lhs];
                            let rhs_ty = self.tys[self.file][*rhs];

                            if let Some(output_ty) = op.get_possible_output_ty(&lhs_ty, &rhs_ty) {
                                if *lhs_ty != Ty::Unknown
                                    && *rhs_ty != Ty::Unknown
                                    && !op.can_perform(&output_ty.max_ty)
                                {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::BinaryOpMismatch {
                                            op: *op,
                                            first: lhs_ty,
                                            second: rhs_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                let max_ty = output_ty.max_ty.into();

                                self.replace_weak_tys(*lhs, max_ty);
                                self.replace_weak_tys(*rhs, max_ty);

                                output_ty.final_output_ty.into()
                            } else {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::BinaryOpMismatch {
                                        op: *op,
                                        first: lhs_ty,
                                        second: rhs_ty,
                                    },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                op.default_ty().into()
                            }
                        }
                        Expr::Unary { expr, op } => {
                            let expr_ty = self.tys[self.file][*expr];

                            if !op.can_perform(&expr_ty) {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::UnaryOpMismatch {
                                        op: *op,
                                        ty: expr_ty,
                                    },
                                    file: self.file,
                                    expr: Some(*expr),
                                    range: self.bodies.range_for_expr(*expr),
                                    help: None,
                                });

                                op.default_ty().into()
                            } else {
                                let output = op.get_possible_output_ty(expr_ty);

                                self.replace_weak_tys(*expr, output);

                                output
                            }
                        }
                        Expr::Paren(expr) => match expr {
                            Some(expr) => self.tys[self.file][*expr],
                            None => Ty::Void.into(),
                        },
                        Expr::Block { stmts, tail_expr } => {
                            let label = self.bodies.block_to_scope_id(expr);

                            let mut no_eval = false;

                            for stmt in stmts {
                                match &self.bodies[*stmt] {
                                    Stmt::Break { .. } | Stmt::Continue { .. } => no_eval = true,
                                    Stmt::Expr(expr)
                                        if label.is_none()
                                            && *self.tys[self.file][*expr] == Ty::NoEval =>
                                    {
                                        no_eval = true
                                    }
                                    _ => {}
                                }
                            }

                            match tail_expr {
                                Some(tail) => {
                                    let tail_ty = self.tys[self.file][*tail];

                                    // there might've been a break within this block
                                    // that break would've set the type of this block.
                                    // there also could've been breaks within the tail expression,
                                    // so we have to get this here, after we processed the statements and the
                                    // tail
                                    let previous_ty =
                                        self.tys[self.file].expr_tys.get(expr).copied();

                                    match previous_ty {
                                        Some(previous_ty) => {
                                            if let Some(max) = self.expect_block_match(
                                                Some(*tail),
                                                tail_ty,
                                                expr,
                                                previous_ty,
                                            ) {
                                                // if there was a previous_ty, then there must've been a break,
                                                // and so this block must have a scope id
                                                let id =
                                                    self.bodies.block_to_scope_id(expr).unwrap();
                                                for usage in self.bodies.scope_id_usages(id) {
                                                    if let hir::Stmt::Break {
                                                        value: Some(value),
                                                        ..
                                                    } = self.bodies[*usage]
                                                    {
                                                        self.replace_weak_tys(value, max);
                                                    }
                                                }

                                                max
                                            } else {
                                                Ty::Unknown.into()
                                            }
                                        }
                                        None => tail_ty,
                                    }
                                }
                                None if no_eval => {
                                    let previous_ty =
                                        self.tys[self.file].expr_tys.get(expr).copied();

                                    // if there is no previous type but this block always breaks
                                    // it is 100% certain that the break was for an upper block.
                                    // it is then safe to say this block is "noeval"
                                    // (meaning that it never reaches it's own end)
                                    previous_ty.unwrap_or_else(|| Ty::NoEval.into())
                                }
                                None => {
                                    // if there were no breaks, Void,
                                    // if there was a break, make sure it's Void
                                    if let Some(previous_ty) =
                                        self.tys[self.file].expr_tys.get(expr).copied()
                                    {
                                        if let Some(max) = self.expect_block_match(
                                            Some(expr),
                                            Ty::Void.into(),
                                            expr,
                                            previous_ty,
                                        ) {
                                            max
                                        } else {
                                            Ty::Unknown.into()
                                        }
                                    } else {
                                        Ty::Void.into()
                                    }
                                }
                            }
                        }
                        Expr::If {
                            condition,
                            body,
                            else_branch,
                        } => {
                            let cond_ty = self.tys[self.file][*condition];
                            self.expect_match(cond_ty, Ty::Bool.into(), *condition);

                            let body_ty = self.tys[self.file][*body];

                            if let Some(else_branch) = else_branch {
                                let else_ty = self.tys[self.file][*else_branch];

                                if let Some(real_ty) = body_ty.max(&else_ty) {
                                    let real_ty = real_ty.into();
                                    self.replace_weak_tys(*body, real_ty);
                                    self.replace_weak_tys(*else_branch, real_ty);
                                    real_ty
                                } else {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::IfMismatch {
                                            found: else_ty,
                                            expected: body_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                }
                            } else {
                                if *body_ty != Ty::NoEval
                                    && !body_ty.is_void()
                                    && !body_ty.is_unknown()
                                {
                                    // only get the range if the body isn't unknown
                                    // otherwise we might be getting the range of something that doesn't exist
                                    let help_range = match &self.bodies[*body] {
                                        Expr::Block {
                                            tail_expr: Some(tail_expr),
                                            ..
                                        } => self.bodies.range_for_expr(*tail_expr),
                                        _ => self.bodies.range_for_expr(*body),
                                    };

                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::MissingElse { expected: body_ty },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: Some(TyDiagnosticHelp {
                                            kind: TyDiagnosticHelpKind::IfReturnsTypeHere {
                                                found: body_ty,
                                            },
                                            range: help_range,
                                        }),
                                    });
                                }

                                if *body_ty == Ty::NoEval {
                                    // if the body is noeval, but there isn't an else block,
                                    // it's uncertain whether or not the noeval will actually be
                                    // reached.
                                    //
                                    // tldr; the condition could allow this block to be evaluated
                                    Ty::Void.into()
                                } else {
                                    body_ty
                                }
                            }
                        }
                        Expr::While { condition, body } => {
                            if let Some(condition) = condition {
                                let cond_ty = self.tys[self.file][*condition];
                                self.expect_match(cond_ty, Ty::Bool.into(), *condition);
                            }
                            let body_ty = self.tys[self.file][*body];
                            self.expect_match(body_ty, Ty::Void.into(), *body);

                            if let Some(previous_ty) = self.tys[self.file].expr_tys.get(expr) {
                                *previous_ty
                            } else {
                                Ty::Void.into()
                            }
                        }
                        Expr::Local(local) => self.tys[self.file].local_tys[*local],
                        Expr::Param { idx, .. } => self.param_tys[*idx as usize],
                        Expr::LocalGlobal(name) => {
                            let fqn = hir::Fqn {
                                file: self.file,
                                name: name.name,
                            };

                            let sig = self
                                .tys
                                .signatures
                                .get(&fqn)
                                .ok_or_else(|| vec![Inferrable::Global(fqn)])?;

                            if *sig.0 == Ty::NotYetResolved {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::NotYetResolved { fqn },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            } else {
                                sig.0
                            }
                        }
                        Expr::Member { previous, field } => {
                            let previous_ty = self.tys[self.file][*previous];
                            match previous_ty.as_ref() {
                                Ty::File(file) => {
                                    let fqn = hir::Fqn {
                                        file: *file,
                                        name: field.name,
                                    };

                                    match self.world_index.definition(fqn) {
                                        hir::DefinitionStatus::Defined => {
                                            let sig = self
                                                .tys
                                                .signatures
                                                .get(&fqn)
                                                .ok_or_else(|| vec![Inferrable::Global(fqn)])?;

                                            if *sig.0 == Ty::NotYetResolved {
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::NotYetResolved { fqn },
                                                    file: self.file,
                                                    expr: Some(expr),
                                                    range: self.bodies.range_for_expr(expr),
                                                    help: None,
                                                });

                                                Ty::Unknown.into()
                                            } else {
                                                sig.0
                                            }
                                        }
                                        hir::DefinitionStatus::UnknownFile => {
                                            unreachable!("a module wasn't added: {:?}", file)
                                        }
                                        hir::DefinitionStatus::UnknownDefinition => {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::UnknownFqn { fqn },
                                                file: self.file,
                                                expr: Some(expr),
                                                range: self.bodies.range_for_expr(expr),
                                                help: None,
                                            });

                                            Ty::Unknown.into()
                                        }
                                    }
                                }
                                _ => {
                                    // because it's annoying to do `foo^.bar`, this code lets you do `foo.bar`
                                    let mut deref_ty = previous_ty;
                                    while let Some((_, sub_ty)) = deref_ty.as_pointer() {
                                        deref_ty = sub_ty;
                                    }

                                    if let Some((_, ty)) = deref_ty.as_struct().and_then(|fields| {
                                        fields.into_iter().find(|(name, _)| *name == field.name)
                                    }) {
                                        ty
                                    } else if let Some((sub_ty, field_name)) =
                                        deref_ty.as_slice().and_then(|sub_ty| {
                                            ["len", "ptr"]
                                                .into_iter()
                                                .find(|f| f == &self.interner.lookup(field.name.0))
                                                .map(|f| (sub_ty, f))
                                        })
                                    {
                                        if field_name == "len" {
                                            Ty::UInt(u8::MAX).into()
                                        } else {
                                            Ty::Pointer {
                                                mutable: false,
                                                sub_ty,
                                            }
                                            .into()
                                        }
                                    } else if deref_ty.is_array()
                                        && self.interner.lookup(field.name.0) == "len"
                                    {
                                        Ty::UInt(u8::MAX).into()
                                    } else {
                                        if !previous_ty.is_unknown() {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::NonExistentMember {
                                                    member: field.name.0,
                                                    found_ty: previous_ty,
                                                },
                                                file: self.file,
                                                expr: Some(expr),
                                                range: self.bodies.range_for_expr(expr),
                                                help: None,
                                            });
                                        }

                                        Ty::Unknown.into()
                                    }
                                }
                            }
                        }
                        Expr::Call { callee, args } => {
                            let callee_ty = self.tys[self.file][*callee];

                            if let Some((params, return_ty)) = callee_ty.clone().as_function() {
                                if params.len() != args.len() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::MismatchedArgCount {
                                            found: args.len(),
                                            expected: params.len(),
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                for (idx, arg) in args.iter().enumerate() {
                                    let arg_ty = self.tys[self.file][*arg];

                                    if idx >= params.len() {
                                        continue;
                                    }
                                    let param_ty = params[idx];

                                    self.expect_match(arg_ty, param_ty, *arg);

                                    self.replace_weak_tys(*arg, param_ty);
                                }

                                return_ty
                            } else {
                                if *callee_ty != Ty::Unknown {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::CalledNonFunction {
                                            found: callee_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                Ty::Unknown.into()
                            }
                        }
                        Expr::Lambda(lambda) => {
                            let hir::Lambda {
                                params,
                                return_ty,
                                body,
                                is_extern,
                                ..
                            } = &self.bodies[*lambda];

                            let is_type = !is_extern
                                && return_ty.is_some()
                                && self.bodies[*body] == hir::Expr::Missing;

                            let return_ty = if let Some(return_ty) = return_ty {
                                self.const_ty(*return_ty)?
                            } else {
                                Ty::Void.into()
                            };

                            let param_tys = params
                                .iter()
                                .map(|param| self.const_ty(param.ty))
                                .collect::<InferResult<Vec<_>>>()?;

                            let ty = Ty::Function {
                                param_tys: param_tys.clone(),
                                return_ty,
                            }
                            .into();

                            if is_type {
                                self.tys[self.file].meta_tys.insert(expr, ty);

                                Ty::Type.into()
                            } else {
                                self.to_infer.insert(Inferrable::Lambda(FQLambda {
                                    file: self.file,
                                    expr,
                                    lambda: *lambda,
                                }));

                                ty
                            }
                        }
                        Expr::Comptime(comptime) => {
                            let hir::Comptime { body } = self.bodies[*comptime];

                            let ty = self.tys[self.file][body];

                            if ty.is_pointer() || ty.is_function() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::ComptimePointer,
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            } else if *ty == Ty::Type {
                                self.const_ty(expr)?;
                                ty
                            } else {
                                ty
                            }
                        }
                        Expr::StructLiteral {
                            ty: Some(ty_expr),
                            members: member_values,
                        } => 'struct_lit: {
                            let expected_ty = self.const_ty(*ty_expr)?;

                            // IndexMap is used to make sure errors are emitted in a logical order

                            let found_member_tys = member_values
                                .iter()
                                .copied()
                                .filter_map(|(name, value)| {
                                    name.map(|name| {
                                        (name.name, (name.range, value, self.tys[self.file][value]))
                                    })
                                })
                                .collect::<IndexMap<_, _>>();

                            let expected_tys = match expected_ty.as_struct() {
                                Some(f) => f,
                                None => {
                                    self.tys[self.file]
                                        .expr_tys
                                        .insert(expr, Ty::Unknown.into());

                                    break 'struct_lit Ty::Unknown.into();
                                }
                            }
                            .into_iter()
                            .collect::<IndexMap<_, _>>();

                            for (
                                found_member_name,
                                (found_member_range, found_member_expr, found_member_ty),
                            ) in found_member_tys.iter()
                            {
                                if let Some(expected_member_ty) =
                                    expected_tys.get(found_member_name)
                                {
                                    if self.expect_match(
                                        *found_member_ty,
                                        *expected_member_ty,
                                        *found_member_expr,
                                    ) {
                                        self.replace_weak_tys(
                                            *found_member_expr,
                                            *expected_member_ty,
                                        );
                                    }
                                } else {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::NonExistentMember {
                                            member: found_member_name.0,
                                            found_ty: expected_ty,
                                        },
                                        file: self.file,
                                        expr: Some(*found_member_expr),
                                        range: *found_member_range,
                                        help: None,
                                    })
                                }
                            }

                            for expected_member_name in expected_tys
                                .iter()
                                .filter(|(_, ty)| !ty.is_unknown())
                                .map(|(name, _)| name)
                            {
                                if found_member_tys.get(expected_member_name).is_none() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::StructLiteralMissingMember {
                                            member: expected_member_name.0,
                                            expected_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    })
                                }
                            }

                            expected_ty
                        }
                        Expr::StructLiteral {
                            ty: None,
                            members: member_values,
                        } => Ty::Struct {
                            anonymous: true,
                            fqn: None,
                            uid: 0,
                            members: member_values
                                .iter()
                                .copied()
                                .filter_map(|(name, value)| {
                                    name.map(|name| (name.name, self.tys[self.file][value]))
                                })
                                .collect(),
                        }
                        .into(),
                        Expr::Distinct { .. } | Expr::PrimitiveTy(_) => {
                            // resolving the type might reveal diagnostics such as recursive types
                            self.const_ty(expr)?;
                            Ty::Type.into()
                        }
                        Expr::StructDecl { .. } => {
                            self.const_ty(expr)?;
                            Ty::Type.into()
                        }
                        Expr::Import(file_name) => Ty::File(*file_name).into(),
                    };

                    self.tys[self.file].expr_tys.insert(expr, ty);
                }
                Descendant::Stmt(stmt) => {
                    if self.inferred_stmts.contains(&(self.file, stmt)) {
                        continue;
                    }

                    match self.bodies[stmt] {
                        Stmt::Expr(expr) => {
                            self.find_usages(&[expr], stmt);
                        }
                        Stmt::LocalDef(local_def) => {
                            let def_body = &self.bodies[local_def];

                            if let Some(ty_annotation_expr) = def_body.ty {
                                let ty_annotation = self.const_ty(ty_annotation_expr)?;

                                // the definition has an annotation, so the value should match
                                if let Some(value) = def_body.value {
                                    let value_ty = self.tys[self.file][value];
                                    if self.expect_match(value_ty, ty_annotation, value)
                                        && self.replace_weak_tys(value, ty_annotation)
                                    {
                                        self.tys[self.file].expr_tys.insert(value, ty_annotation);
                                    }
                                } else if !ty_annotation.has_default_value() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::DeclTypeHasNoDefault {
                                            ty: ty_annotation,
                                        },
                                        file: self.file,
                                        expr: Some(ty_annotation_expr),
                                        range: self.bodies.range_for_expr(ty_annotation_expr),
                                        help: None,
                                    });
                                }

                                self.tys[self.file]
                                    .local_tys
                                    .insert(local_def, ty_annotation);
                            } else {
                                // the definition does not have an annotation,
                                // so use the type of it's value
                                let value_ty = def_body
                                    .value
                                    .map(|value| self.tys[self.file][value])
                                    .unwrap_or(Ty::Unknown.into());
                                self.tys[self.file].local_tys.insert(local_def, value_ty);
                            }

                            if let Some(value) = def_body.value {
                                self.find_usages(&[value], stmt);
                            }
                        }
                        Stmt::Assign(assign) => {
                            let assign_body = &self.bodies[assign];

                            let source_ty = self.tys[self.file][assign_body.dest];
                            let value_ty = self.tys[self.file][assign_body.value];

                            let help = self
                                .get_mutability(assign_body.dest, true, false)
                                .into_diagnostic();

                            if help.is_some() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::CannotMutate,
                                    file: self.file,
                                    // making expr the source isn't technically correct, but it works
                                    expr: Some(assign_body.dest),
                                    range: assign_body.range,
                                    help,
                                })
                            } else if source_ty.is_weak_replaceable_by(&value_ty) {
                                self.replace_weak_tys(assign_body.dest, source_ty);
                            } else if self.expect_match(value_ty, source_ty, assign_body.value) {
                                self.replace_weak_tys(assign_body.value, source_ty);
                            }

                            self.find_usages(&[assign_body.dest, assign_body.value], stmt);
                        }
                        Stmt::Break { label: None, .. } => {}
                        Stmt::Break {
                            label: Some(label),
                            value,
                            ..
                        } => {
                            let referenced_expr = self.bodies[label];

                            let value_ty = value.map_or_else(
                                || Ty::Void.into(),
                                |value| self.tys[self.file][value],
                            );

                            let must_be_void = matches!(
                                self.bodies[referenced_expr],
                                Expr::While {
                                    condition: Some(_),
                                    ..
                                }
                            );

                            match self.tys[self.file].expr_tys.get(referenced_expr) {
                                Some(expected_ty) => {
                                    self.expect_block_match(
                                        value,
                                        value_ty,
                                        referenced_expr,
                                        *expected_ty,
                                    );
                                }
                                None => {
                                    if must_be_void && !value_ty.is_void() {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::Mismatch {
                                                expected: Ty::Void.into(),
                                                found: value_ty,
                                            },
                                            file: self.file,
                                            expr: value,
                                            range: self.bodies.range_for_expr(value.unwrap()),
                                            help: None,
                                        });

                                        self.tys[self.file]
                                            .expr_tys
                                            .insert(referenced_expr, Ty::Unknown.into());
                                    } else {
                                        self.tys[self.file]
                                            .expr_tys
                                            .insert(referenced_expr, value_ty);
                                    }
                                }
                            }
                        }
                        Stmt::Continue { .. } => {}
                        Stmt::Defer { expr, .. } => {
                            self.find_usages(&[expr], stmt);
                        }
                    }

                    self.inferred_stmts.insert((self.file, stmt));
                }
            };
        }

        Ok(self.tys[self.file][expr])
    }

    /// Only call for blocks which had their type previously set by a `break`
    ///
    /// returns the max of the found expression and the current type of the block
    fn expect_block_match(
        &mut self,
        found_expr: Option<Idx<hir::Expr>>,
        found_ty: Intern<Ty>,
        block_expr: Idx<hir::Expr>,
        block_ty: Intern<Ty>,
    ) -> Option<Intern<Ty>> {
        if found_ty.is_unknown() || block_ty.is_unknown() {
            return None;
        }

        if let Some(max) = block_ty.max(&found_ty) {
            let max = max.into();
            self.tys[self.file].expr_tys[block_expr] = max;
            if let Some(found_expr) = found_expr {
                self.replace_weak_tys(found_expr, max);
            }

            Some(max)
        } else {
            // there must be a usage since the block has a type
            let id = self.bodies.block_to_scope_id(block_expr).unwrap();
            let first_usage = self.bodies.scope_id_usages(id).iter().next().unwrap();

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch {
                    expected: block_ty,
                    found: found_ty,
                },
                file: self.file,
                expr: Some(found_expr.unwrap_or(block_expr)),
                range: self.bodies.range_for_expr(found_expr.unwrap_or(block_expr)),
                help: Some(TyDiagnosticHelp {
                    kind: TyDiagnosticHelpKind::BreakHere { break_ty: block_ty },
                    range: self.bodies.range_for_stmt(*first_usage),
                }),
            });

            self.tys[self.file].expr_tys[block_expr] = Ty::Unknown.into();

            None
        }
    }

    /// If found does not match expected, an error is thrown at the expression
    pub(crate) fn expect_match(
        &mut self,
        found: Intern<Ty>,
        expected: Intern<Ty>,
        expr: Idx<hir::Expr>,
    ) -> bool {
        // if the expression we're checking against is an
        // int literal (which can be inferred into any int type),
        // then we can just quickly set it's type here
        if let (hir::Expr::IntLiteral(num), Ty::IInt(bit_width) | Ty::UInt(bit_width)) =
            (&self.bodies[expr], expected.as_ref())
        {
            if *bit_width != u8::MAX {
                self.tys[self.file].expr_tys[expr] = expected;
            }

            if let Some(max_size) = expected.get_max_int_size() {
                if *num > max_size {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IntTooBigForType {
                            found: *num,
                            max: max_size,
                            ty: expected,
                        },
                        file: self.file,
                        expr: Some(expr),
                        range: self.bodies.range_for_expr(expr),
                        help: None,
                    });
                }
            }

            return true;
        }

        if found.is_unknown() || expected.is_unknown() {
            // return false without throwing an error
            return false;
        }

        if !found.can_fit_into(&expected) {
            let help = match self.bodies[expr] {
                hir::Expr::Block {
                    tail_expr: Some(tail_expr),
                    ..
                } => Some(TyDiagnosticHelp {
                    kind: TyDiagnosticHelpKind::TailExprReturnsHere,
                    range: self.bodies.range_for_expr(tail_expr),
                }),
                _ => None,
            };

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch { expected, found },
                file: self.file,
                expr: Some(expr),
                range: self.bodies.range_for_expr(expr),
                help,
            });

            false
        } else {
            true
        }
    }

    fn fqn_to_ty(
        &mut self,
        fqn: hir::Fqn,
        file_expr: Option<Idx<hir::Expr>>,
        total_expr: Idx<hir::Expr>,
        name_range: TextRange,
    ) -> InferResult<Intern<Ty>> {
        match self.world_index.definition(fqn) {
            hir::DefinitionStatus::Defined => {
                // this should also set the meta type
                let ty = self
                    .tys
                    .signatures
                    .get(&fqn)
                    .ok_or_else(|| vec![Inferrable::Global(fqn)])?
                    .0;

                if *ty == Ty::Unknown {
                    return Ok(Ty::Unknown.into());
                }

                if *ty == Ty::NotYetResolved {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::NotYetResolved { fqn },
                        file: self.file,
                        expr: Some(total_expr),
                        range: name_range,
                        help: None,
                    });

                    return Ok(Ty::Unknown.into());
                }

                if *ty != Ty::Type {
                    if !ty.is_unknown() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::Mismatch {
                                expected: Ty::Type.into(),
                                found: ty,
                            },
                            file: self.file,
                            expr: Some(total_expr),
                            range: name_range,
                            help: None,
                        });
                    }
                    return Ok(Ty::Unknown.into());
                }

                let global_body = self.world_bodies.body(fqn);

                // most global bodies will already have set `meta_tys` with the
                // actual type, but occasionally something slips through, and since
                // it'd be a lot of wasted memory to insert meta_tys for locals and
                // member accesses, and indexes, etc. that may never be used, it's
                // better to just calculate these here.
                // an example of this is a type alias.
                // ```
                // Bar :: distinct i32;
                // Foo :: Bar;
                //
                // main :: () {
                //     x : Foo = 42;
                // }
                // ```
                // in this case we might code something special in the `infer_expr`
                // code to calculate the meta type if the local is constant, but that
                // would waste a lot of space and what about members? it's just too much
                let old_file = std::mem::replace(&mut self.file, fqn.file);
                let actual_ty = self.const_ty(global_body)?;
                self.file = old_file;

                // it'd be better to mutate the fqn, but that would invalidate the hash
                // within the internment crate
                Ok(match actual_ty.as_ref() {
                    Ty::Distinct {
                        fqn: None,
                        sub_ty: ty,
                        uid,
                    } => Ty::Distinct {
                        fqn: Some(fqn),
                        uid: *uid,
                        sub_ty: *ty,
                    }
                    .into(),
                    Ty::Struct {
                        anonymous,
                        fqn: None,
                        members,
                        uid,
                    } => Ty::Struct {
                        anonymous: *anonymous,
                        fqn: Some(fqn),
                        members: members.clone(),
                        uid: *uid,
                    }
                    .into(),
                    _ => actual_ty,
                })
            }
            hir::DefinitionStatus::UnknownFile => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFile { file: fqn.file },
                    file: self.file,
                    expr: file_expr,
                    range: self.bodies.range_for_expr(file_expr.unwrap()),
                    help: None,
                });
                Ok(Ty::Unknown.into())
            }
            hir::DefinitionStatus::UnknownDefinition => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFqn { fqn },
                    file: self.file,
                    expr: file_expr,
                    range: self.bodies.range_for_expr(file_expr.unwrap()),
                    help: None,
                });
                Ok(Ty::Unknown.into())
            }
        }
    }

    pub(crate) fn const_ty(&mut self, expr: Idx<hir::Expr>) -> InferResult<Intern<Ty>> {
        if let Some(meta_ty) = self.tys[self.file].get_meta_ty(expr) {
            return Ok(meta_ty);
        }

        let include_local_value = |local| {
            let local_def = &self.bodies[local];
            let local_ty = self.tys[self.file].local_tys[local];

            *local_ty == Ty::Type && !local_def.mutable
        };

        let descendants = self.bodies.descendants(
            expr,
            hir::DescentOpts::Types {
                include_local_value: &include_local_value,
            },
        );

        for descendant in descendants.collect_vec().into_iter().rev() {
            match descendant {
                Descendant::Expr(expr) => {
                    if self.tys[self.file].get_meta_ty(expr).is_some() {
                        continue;
                    }

                    let ty = match &self.bodies[expr] {
                        Expr::Missing => Ty::Unknown.into(),
                        Expr::Ref { mutable, expr } => {
                            let sub_ty = self.tys[self.file].get_meta_ty(*expr).unwrap();

                            Ty::Pointer {
                                mutable: *mutable,
                                sub_ty,
                            }
                            .into()
                        }
                        Expr::Local(local_def) => 'branch: {
                            let local_ty = self.tys[self.file].local_tys[*local_def];

                            if *local_ty == Ty::Unknown {
                                break 'branch Ty::Unknown.into();
                            }

                            if *local_ty != Ty::Type {
                                if !local_ty.is_unknown() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::Mismatch {
                                            expected: Ty::Type.into(),
                                            found: self.tys[self.file].local_tys[*local_def],
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                break 'branch Ty::Unknown.into();
                            }

                            let local_def = &self.bodies[*local_def];

                            if local_def.mutable {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::LocalTyIsMutable,
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: Some(TyDiagnosticHelp {
                                        kind: TyDiagnosticHelpKind::MutableVariable,
                                        range: local_def.range,
                                    }),
                                });

                                break 'branch Ty::Unknown.into();
                            }

                            // this protects against cases like `x ::;`
                            if let Some(value) = local_def.value {
                                self.tys[self.file].get_meta_ty(value).unwrap()
                            } else {
                                Ty::Unknown.into()
                            }
                        }
                        Expr::LocalGlobal(name) => self.fqn_to_ty(
                            hir::Fqn {
                                file: self.file,
                                name: name.name,
                            },
                            None,
                            expr,
                            name.range,
                        )?,
                        Expr::Param { .. } => {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::ParamNotATy,
                                file: self.file,
                                expr: Some(expr),
                                range: self.bodies.range_for_expr(expr),
                                help: None,
                            });

                            Ty::Unknown.into()
                        }
                        Expr::Member { previous, field } => {
                            let previous_ty = self.infer_expr(*previous)?;

                            match previous_ty.as_ref() {
                                Ty::File(file) => self.fqn_to_ty(
                                    hir::Fqn {
                                        file: *file,
                                        name: field.name,
                                    },
                                    Some(*previous),
                                    expr,
                                    field.range,
                                )?,
                                _ => {
                                    let expr_ty = self.infer_expr(expr)?;
                                    if !expr_ty.is_unknown() {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::Mismatch {
                                                expected: Ty::Type.into(),
                                                found: expr_ty,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help: None,
                                        });
                                    }

                                    Ty::Unknown.into()
                                }
                            }
                        }
                        Expr::PrimitiveTy(ty) => Ty::from_primitive(*ty).into(),
                        Expr::ArrayDecl { size, ty } => 'branch: {
                            let sub_ty = self.tys[self.file].meta_tys[*ty];

                            if let Some(size) = size {
                                // we must infer it manually because it might not
                                // have been inferred.
                                // todo: remove recursion
                                self.infer_expr(*size)?;

                                let usize_ty = Ty::UInt(u8::MAX).into();
                                if !self.expect_match(self.tys[self.file][*size], usize_ty, *size) {
                                    break 'branch Ty::Unknown.into();
                                }

                                self.replace_weak_tys(*size, usize_ty);

                                let expr_const = self.get_const(*size);
                                if !expr_const.is_const() {
                                    println!("not const {expr_const:?}");
                                    if expr_const.should_report_not_const() {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::ArraySizeNotConst,
                                            file: self.file,
                                            range: self.bodies.range_for_expr(*size),
                                            expr: Some(*size),
                                            help: None,
                                        });
                                    }
                                    break 'branch Ty::Unknown.into();
                                }

                                match self.const_data(self.file, *size)? {
                                    Some(ComptimeResult::Integer { num, .. }) => Ty::Array {
                                        anonymous: false,
                                        size: num,
                                        sub_ty,
                                    }
                                    .into(),
                                    _ => {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::ArraySizeNotInt,
                                            file: self.file,
                                            range: self.bodies.range_for_expr(*size),
                                            expr: Some(*size),
                                            help: None,
                                        });

                                        Ty::Unknown.into()
                                    }
                                }
                            } else {
                                Ty::Slice { sub_ty }.into()
                            }
                        }
                        Expr::Distinct { uid, ty } => Ty::Distinct {
                            fqn: None,
                            uid: *uid,
                            sub_ty: self.tys[self.file].meta_tys[*ty],
                        }
                        .into(),
                        Expr::StructDecl { uid, members } => Ty::Struct {
                            anonymous: false,
                            fqn: None,
                            uid: *uid,
                            members: members
                                .iter()
                                .cloned()
                                .filter_map(|(name, ty)| name.map(|name| (name, ty)))
                                .map(|(name, ty)| (name.name, self.tys[self.file].meta_tys[ty]))
                                .collect(),
                        }
                        .into(),
                        Expr::Lambda(lambda) => {
                            let hir::Lambda {
                                params,
                                return_ty,
                                body,
                                is_extern,
                                ..
                            } = &self.bodies[*lambda];

                            let return_ty = if let Some(return_ty) = return_ty {
                                self.tys[self.file].meta_tys[*return_ty]
                            } else {
                                Ty::Void.into()
                            };

                            let param_tys = params
                                .iter()
                                .map(|param| self.tys[self.file].meta_tys[param.ty])
                                .collect::<Vec<_>>();

                            let ty = Ty::Function {
                                param_tys: param_tys.clone(),
                                return_ty,
                            }
                            .into();

                            // if the function has a body (or is extern), then it isn't a type
                            if *is_extern || self.bodies[*body] != hir::Expr::Missing {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::Mismatch {
                                        expected: Ty::Type.into(),
                                        found: ty,
                                    },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            } else {
                                ty
                            }
                        }
                        Expr::Comptime(comptime) => {
                            let hir::Comptime { body } = self.bodies[*comptime];

                            let ty = self.infer_expr(body)?;

                            if *ty == Ty::Type {
                                self.tys[self.file].expr_tys.insert(expr, ty);

                                if self.is_safe_to_compile(body)? {
                                    match (self.eval_comptime)(
                                        FQComptime {
                                            file: self.file,
                                            expr,
                                            comptime: *comptime,
                                        },
                                        self.tys,
                                    ) {
                                        ComptimeResult::Type(ty) => ty,
                                        _ => unreachable!(),
                                    }
                                } else {
                                    // println!("#{} is not safe to compile", body.into_raw());
                                    Ty::Unknown.into()
                                }
                            } else {
                                Ty::Unknown.into()
                            }
                        }
                        Expr::Paren(Some(paren_expr)) => {
                            // todo: remove recursion
                            self.const_ty(*paren_expr)?
                        }
                        // todo: should we remove the void type?
                        Expr::Paren(None) => Ty::Void.into(),
                        Expr::Block { .. } => todo!("blocks as types"),
                        _ => {
                            // todo: remove recursion
                            let expr_ty = self.infer_expr(expr)?;

                            if !expr_ty.is_unknown() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::Mismatch {
                                        expected: Ty::Type.into(),
                                        found: expr_ty,
                                    },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });
                            }

                            Ty::Unknown.into()
                        }
                    };

                    self.tys[self.file].meta_tys.insert(expr, ty);
                }
                Descendant::Stmt(_) => unreachable!(),
            }
        }

        Ok(self.tys[self.file].meta_tys[expr])
    }

    pub(crate) fn const_data(
        &mut self,
        file: hir::FileName,
        expr: Idx<hir::Expr>,
    ) -> InferResult<Option<ComptimeResult>> {
        if !self.tys[file].expr_tys.contains_idx(expr) {
            panic!(
                "You should have inferred {} #{} before trying to call `const_data` on it",
                file.debug(self.interner),
                expr.into_raw()
            );
        }

        match &self.world_bodies[file][expr] {
            Expr::IntLiteral(num) => Ok(Some(ComptimeResult::Integer {
                num: *num,
                bit_width: 32,
            })),
            Expr::FloatLiteral(num) => Ok(Some(ComptimeResult::Float {
                num: *num,
                bit_width: 32,
            })),
            Expr::Comptime(comptime) => {
                let hir::Comptime { body } = self.world_bodies[file][*comptime];

                if self.is_safe_to_compile(body)? {
                    Ok(Some((self.eval_comptime)(
                        FQComptime {
                            file,
                            expr,
                            comptime: *comptime,
                        },
                        self.tys,
                    )))
                } else {
                    // println!("#{} is not safe to compile", body.into_raw());
                    Ok(None)
                }
            }
            Expr::Local(local_def) => {
                let local_def = &self.world_bodies[file][*local_def];

                assert!(
                    local_def.value.is_some(),
                    "`get_const` should have set this type of variable to non-const"
                );

                // todo: remove recursion
                self.const_data(file, local_def.value.unwrap())
            }
            Expr::LocalGlobal(global) => {
                let fqn = hir::Fqn {
                    file,
                    name: global.name,
                };

                self.const_data(file, self.world_bodies.body(fqn))
            }
            Expr::Member { previous, field } => match self.tys[self.file][*previous].as_ref() {
                Ty::File(file) => {
                    let fqn = hir::Fqn {
                        file: *file,
                        name: field.name,
                    };

                    self.const_data(*file, self.world_bodies.body(fqn))
                }
                _ => Ok(None),
            },
            // todo: add the rest of the possible expressions in `is_const`
            _ => Ok(None),
        }
    }

    // todo: this is actually a great opportunity for fuzzing to make sure this function never
    // returns true when something was actually unsafe. the fuzzer has already been updated it just
    // needs to be used.
    pub(crate) fn is_safe_to_compile(&mut self, expr: Idx<hir::Expr>) -> InferResult<bool> {
        let mut checking_stack = vec![(
            self.current_inferring,
            self.bodies
                .descendants(
                    expr,
                    hir::DescentOpts::All {
                        include_lambdas: false,
                    },
                )
                .collect_vec(),
        )];

        // println!("desc: {:#?}", descendants);

        let error_exprs: FxHashSet<_> = self
            .diagnostics
            .iter()
            .filter(|d| d.is_error())
            .filter_map(|d| Some((d.file, d.expr?)))
            .collect();

        let mut checked = FxHashSet::default();
        checked.insert(self.current_inferring);

        loop {
            let Some((top_inferring, top_list)) = checking_stack.last_mut() else {
                break;
            };

            let file = top_inferring.file();

            let Some(desc) = top_list.pop() else {
                checking_stack.pop();
                continue;
            };

            let print_dbg = cfg!(debug_assertions);

            match desc {
                Descendant::Expr(expr) => {
                    // println!("checking #{}", expr.into_raw());

                    if error_exprs.contains(&(file, expr)) {
                        if print_dbg {
                            println!(
                                "{}:{} unsafe {} #{}",
                                file!(),
                                line!(),
                                file.debug(self.interner),
                                expr.into_raw()
                            );
                        }
                        return Ok(false);
                    }

                    if let Some(ty) = self.tys[file].get_meta_ty(expr) {
                        if ty.is_unknown() {
                            if print_dbg {
                                println!(
                                    "{}:{} unsafe {} #{}",
                                    file!(),
                                    line!(),
                                    file.debug(self.interner),
                                    expr.into_raw()
                                );
                            }
                            return Ok(false);
                        }

                        continue;
                    }

                    let Some(ty) = self.tys[file].expr_tys.get(expr) else {
                        if print_dbg {
                            println!(
                                "{}:{} unsafe {} #{}",
                                file!(),
                                line!(),
                                file.debug(self.interner),
                                expr.into_raw()
                            );
                        }
                        return Ok(false);
                    };

                    if ty.is_unknown() {
                        if print_dbg {
                            println!(
                                "{}:{} unsafe {} #{}",
                                file!(),
                                line!(),
                                file.debug(self.interner),
                                expr.into_raw()
                            );
                        }
                        return Ok(false);
                    }

                    match &self.world_bodies[file][expr] {
                        Expr::Missing => {
                            if print_dbg {
                                println!(
                                    "{}:{} unsafe {} #{}",
                                    file!(),
                                    line!(),
                                    file.debug(self.interner),
                                    expr.into_raw()
                                );
                            }
                            return Ok(false);
                        }
                        Expr::IntLiteral(_) => {}
                        Expr::FloatLiteral(_) => {}
                        Expr::BoolLiteral(_) => {}
                        Expr::StringLiteral(_) => {}
                        Expr::CharLiteral(_) => {}
                        Expr::Cast { .. } => {}
                        Expr::Ref { .. } => {}
                        Expr::Deref { .. } => {}
                        Expr::Binary { .. } => {}
                        Expr::Unary { .. } => {}
                        Expr::ArrayDecl { .. } => {}
                        Expr::ArrayLiteral { .. } => {}
                        Expr::Index { .. } => {}
                        Expr::Paren(_) => {}
                        Expr::Block { .. } => {}
                        Expr::If { .. } => {}
                        Expr::While { .. } => {}
                        Expr::Local(_) => {}
                        Expr::LocalGlobal(name) => {
                            let fqn = hir::Fqn {
                                file,
                                name: name.name,
                            };

                            let new_inf = Inferrable::Global(fqn);

                            if checked.contains(&new_inf) {
                                continue;
                            }

                            checked.insert(new_inf);

                            if self.world_bodies.is_extern(fqn) {
                                continue;
                            }

                            if !self.all_inferred.contains(&new_inf) {
                                return Err(vec![new_inf]);
                            }

                            let body = self.world_bodies.body(fqn);

                            checking_stack.push((
                                Inferrable::Global(fqn),
                                self.world_bodies[fqn.file]
                                    .descendants(
                                        body,
                                        hir::DescentOpts::All {
                                            include_lambdas: false,
                                        },
                                    )
                                    .collect(),
                            ));
                        }
                        Expr::Param { .. } => {}
                        Expr::Member { previous, field } => {
                            let previous_ty = self.tys[file][*previous];
                            if let Ty::File(file) = previous_ty.as_ref() {
                                let fqn = hir::Fqn {
                                    file: *file,
                                    name: field.name,
                                };

                                let new_inf = Inferrable::Global(fqn);

                                if checked.contains(&new_inf) {
                                    continue;
                                }

                                checked.insert(new_inf);

                                if self.world_bodies.is_extern(fqn) {
                                    continue;
                                }

                                match self.world_index.definition(fqn) {
                                    hir::DefinitionStatus::Defined => {
                                        let mut deps = Vec::new();

                                        if !self.all_inferred.contains(&Inferrable::Global(fqn)) {
                                            deps.push(Inferrable::Global(fqn));
                                        }

                                        let body = self.world_bodies.body(fqn);

                                        // if let Expr::Lambda(lambda) =
                                        //     self.world_bodies[fqn.file][body]
                                        // {
                                        //     let lambda = Inferrable::Lambda(FQLambda {
                                        //         file: fqn.file,
                                        //         expr: body,
                                        //         lambda,
                                        //     });
                                        //
                                        //     dbg!(lambda);
                                        //
                                        //     if !self.all_inferred.contains(&lambda) {
                                        //         deps.push(lambda);
                                        //     }
                                        // }

                                        if !deps.is_empty() {
                                            return Err(deps);
                                        }

                                        checking_stack.push((
                                            new_inf,
                                            self.world_bodies[fqn.file]
                                                .descendants(
                                                    body,
                                                    hir::DescentOpts::All {
                                                        include_lambdas: false,
                                                    },
                                                )
                                                .collect(),
                                        ));
                                    }
                                    _ => {
                                        if print_dbg {
                                            println!(
                                                "{}:{} unsafe {} #{}",
                                                file!(),
                                                line!(),
                                                file.debug(self.interner),
                                                expr.into_raw()
                                            );
                                        }
                                        return Ok(false);
                                    }
                                }
                            }
                        }
                        Expr::Call { .. } => {}
                        Expr::Lambda(lambda) => {
                            let lambda_body = &self.world_bodies[file][*lambda];
                            let lambda = Inferrable::Lambda(FQLambda {
                                file,
                                expr,
                                lambda: *lambda,
                            });

                            if checked.contains(&lambda) {
                                continue;
                            }

                            checked.insert(lambda);

                            if !self.all_inferred.contains(&lambda) {
                                return Err(vec![lambda]);
                            }

                            let is_type = !lambda_body.is_extern
                                && lambda_body.return_ty.is_some()
                                && self.world_bodies[file][lambda_body.body] == Expr::Missing;

                            // println!(
                            //     "lambda #{} : {} {}",
                            //     expr.into_raw(),
                            //     lambda_body.is_extern,
                            //     is_type
                            // );

                            // check if the lambda is extern, or it is being used as a type
                            if !lambda_body.is_extern && !is_type {
                                checking_stack.push((
                                    lambda,
                                    self.world_bodies[file]
                                        .descendants(
                                            lambda_body.body,
                                            hir::DescentOpts::All {
                                                include_lambdas: false,
                                            },
                                        )
                                        .collect(),
                                ));
                            }
                        }
                        Expr::Comptime(_) => {}
                        Expr::PrimitiveTy(_) => {}
                        Expr::Distinct { .. } => {}
                        Expr::StructDecl { .. } => {}
                        Expr::StructLiteral { .. } => {}
                        Expr::Import(_) => {}
                    }
                }
                Descendant::Stmt(stmt) => match &self.world_bodies[file][stmt] {
                    Stmt::Expr(_) => {}
                    Stmt::LocalDef(_) => {}
                    Stmt::Assign(_) => {}
                    Stmt::Break { label, .. } | Stmt::Continue { label, .. } => {
                        if label.is_none() {
                            if print_dbg {
                                println!(
                                    "{}:{} unsafe {} #{}",
                                    file!(),
                                    line!(),
                                    file.debug(self.interner),
                                    expr.into_raw()
                                );
                            }
                            return Ok(false);
                        }
                    }
                    Stmt::Defer { .. } => {}
                },
            }
        }

        Ok(true)
    }
}

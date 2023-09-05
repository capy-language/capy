use std::collections::HashSet;

use hir::{Expr, LocalDef};
use indexmap::IndexMap;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashSet;
use text_size::TextRange;

use crate::{
    resolved_ty::BinaryOutput, InferenceCtx, LocalUsage, ResolvedTy, Signature, TyDiagnostic,
    TyDiagnosticHelp, TyDiagnosticHelpKind, TyDiagnosticKind, TypedOp, UnaryOutput,
};

macro_rules! current_bodies {
    ($self:ident) => {
        &$self.bodies_map[&$self.current_module.unwrap()]
    };
}

macro_rules! current_module {
    ($self:ident) => {
        $self
            .modules
            .get_mut(&$self.current_module.unwrap())
            .unwrap()
    };
}

macro_rules! current_local_usages {
    ($self:ident) => {
        $self
            .local_usages
            .entry($self.current_module.unwrap())
            .or_default()
    };
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
            ExprMutability::Mutable => None,
        }
    }
}

impl InferenceCtx<'_> {
    pub(crate) fn finish_body_known(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<Intern<ResolvedTy>>>,
        expected_ty: Intern<ResolvedTy>,
        global: bool,
    ) {
        let actual_type = self.finish_body_unknown(body, param_tys, global);
        self.expect_match(actual_type, expected_ty, body);
        self.replace_weak_tys(body, expected_ty);
    }

    pub(crate) fn finish_body_unknown(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<Intern<ResolvedTy>>>,
        global: bool,
    ) -> Intern<ResolvedTy> {
        let old_param_tys = match param_tys {
            Some(new_param_tys) => self.param_tys.replace(new_param_tys),
            None => self.param_tys.take(),
        };
        let old_local_usages = self
            .local_usages
            .insert(self.current_module.unwrap(), Default::default());

        self.infer_expr(body);

        let local_usages = current_local_usages!(self).clone();
        for (def, usages) in local_usages.iter() {
            current_local_usages!(self).get_mut(def).unwrap().clear();

            self.reinfer_usages(usages.clone());
        }

        let mut actual_ty = self.reinfer_expr(body);

        let i32 = ResolvedTy::IInt(32).into();
        if global && self.replace_weak_tys(body, i32) {
            actual_ty = i32;
        }

        if let Some(old_local_usages) = old_local_usages {
            self.local_usages
                .insert(self.current_module.unwrap(), old_local_usages);
        }
        self.param_tys = old_param_tys;

        if global && !self.is_const(body) {
            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::GlobalNotConst,
                module: self.current_module.unwrap(),
                range: current_bodies!(self).range_for_expr(body),
                help: None,
            })
        }

        actual_ty
    }

    fn reinfer_usages(&mut self, usages: FxHashSet<LocalUsage>) {
        for usage in usages {
            match usage {
                LocalUsage::Def(user_local_def) => {
                    let user_local_body = &current_bodies!(self)[user_local_def];

                    let user_local_ty = self.reinfer_expr(user_local_body.value);

                    // if there is no type annotation on the user, then replace it's type
                    if matches!(
                        current_bodies!(self)[user_local_body.ty],
                        hir::Expr::Missing
                    ) {
                        current_module!(self)
                            .local_tys
                            .insert(user_local_def, user_local_ty);
                    }
                }
                LocalUsage::Assign(assign) => {
                    let assign_body = &current_bodies!(self)[assign];

                    self.reinfer_expr(assign_body.source);
                    self.reinfer_expr(assign_body.value);
                }
                LocalUsage::Expr(expr) => {
                    self.reinfer_expr(expr);
                }
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
    /// returns true if `expr` had a weak type, returns false if `expr` had a strong type
    fn replace_weak_tys(&mut self, expr: Idx<hir::Expr>, new_ty: Intern<ResolvedTy>) -> bool {
        let found_ty = &current_module!(self).expr_tys[expr];

        // println!("  replace_weak_tys {:?} {:?}", found_ty, new_ty);
        if !found_ty.is_weak_type_replaceable_by(&new_ty) {
            // println!("no");
            return false;
        }
        // println!("yeah");

        current_module!(self).expr_tys.insert(expr, new_ty);

        match current_bodies!(self)[expr].clone() {
            Expr::IntLiteral(num) => {
                if let Some(max_size) = new_ty.get_max_int_size() {
                    if num > max_size {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IntTooBigForType {
                                found: num,
                                max: max_size,
                                ty: new_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }
                }
            }
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => {
                self.replace_weak_tys(tail_expr, new_ty);
            }
            Expr::If {
                body, else_branch, ..
            } => {
                self.replace_weak_tys(body, new_ty);
                if let Some(else_branch) = else_branch {
                    self.replace_weak_tys(else_branch, new_ty);
                }
            }
            Expr::Comptime(comptime) => {
                let body = current_bodies!(self)[comptime].body;

                self.replace_weak_tys(body, new_ty);
            }
            Expr::Deref { pointer } => {
                let mutable = current_module!(self).expr_tys[expr]
                    .as_pointer()
                    .map(|(mutable, _)| mutable)
                    .unwrap_or_default();

                self.replace_weak_tys(
                    pointer,
                    ResolvedTy::Pointer {
                        mutable,
                        sub_ty: new_ty,
                    }
                    .into(),
                );
            }
            Expr::Ref { expr, .. } => {
                if let Some(sub_ty) = new_ty.as_pointer().map(|(_, sub_ty)| sub_ty) {
                    self.replace_weak_tys(expr, sub_ty);
                }
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.replace_weak_tys(lhs, new_ty);
                self.replace_weak_tys(rhs, new_ty);
            }
            Expr::Unary { expr, .. } => {
                self.replace_weak_tys(expr, new_ty);
            }
            Expr::Local(local_def) => {
                if self.replace_weak_tys(current_bodies!(self)[local_def].value, new_ty) {
                    current_module!(self).local_tys.insert(local_def, new_ty);
                }

                // now get everything that used this variable and make sure the types are correct for those things
                let usages = current_local_usages!(self)
                    .get(local_def)
                    .cloned()
                    .unwrap_or_default();

                // now that we have the usages, clear them so no nasty recursion takes place
                if let Some(usages) = current_local_usages!(self).get_mut(local_def) {
                    usages.clear();
                }

                self.reinfer_usages(usages);

                // self.reinfer_expr(current_bodies!(self)[local_def].value);
            }
            Expr::StructLiteral { fields, .. } => {
                let field_tys = new_ty.as_struct().unwrap();

                for (idx, (_, value)) in fields.into_iter().enumerate() {
                    let new_field_ty = field_tys[idx].1;

                    self.replace_weak_tys(value, new_field_ty);
                }
            }
            _ => {}
        }

        true
    }

    fn is_const(&self, expr: Idx<Expr>) -> bool {
        match &current_bodies!(self)[expr] {
            Expr::Missing
            | Expr::Import(_)
            | Expr::PrimitiveTy { .. }
            | Expr::Comptime(_)
            | Expr::StringLiteral(_)
            | Expr::IntLiteral(_)
            | Expr::FloatLiteral(_)
            | Expr::BoolLiteral(_) => true,
            Expr::Array { items, .. } => items.iter().all(|item| self.is_const(*item)),
            _ => *(self.modules[&self.current_module.unwrap()][expr]) == ResolvedTy::Type,
        }
    }

    /// `deref` allows certain expressions to be mutable
    /// only if they are being mutated through a deref
    fn get_mutability(&self, expr: Idx<Expr>, assignment: bool, deref: bool) -> ExprMutability {
        match &current_bodies!(self)[expr] {
            Expr::Missing => ExprMutability::Mutable,
            Expr::Array { .. } => ExprMutability::Mutable,
            Expr::StructLiteral { .. } => ExprMutability::Mutable,
            Expr::Ref { mutable, .. } => match (*mutable, deref) {
                (true, _) => ExprMutability::Mutable,
                // (true, false) => ExprMutability::NotMutatingRefThroughDeref(
                //     current_bodies!(self).range_for_expr(expr),
                // ),
                _ => ExprMutability::ImmutableRef(current_bodies!(self).range_for_expr(expr)),
            },
            Expr::Deref { pointer } => self.get_mutability(*pointer, assignment, true),
            Expr::Index { array, .. } => self.get_mutability(
                *array,
                assignment,
                deref || self.modules[&self.current_module.unwrap()][*array].is_pointer(),
            ),
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => self.get_mutability(*tail_expr, assignment, deref),
            Expr::Local(local_def) if deref => {
                let local_def = &current_bodies!(self)[*local_def];

                self.get_mutability(local_def.value, false, deref)
            }
            Expr::Local(local_def) if !deref => {
                let local_ty = self.modules[&self.current_module.unwrap()][*local_def];
                let local_def = &current_bodies!(self)[*local_def];

                match local_ty.as_pointer() {
                    Some((mutable, _)) if assignment => {
                        if mutable {
                            ExprMutability::NotMutatingRefThroughDeref(
                                current_bodies!(self).range_for_expr(expr),
                            )
                        } else {
                            ExprMutability::ImmutableRef(
                                current_bodies!(self).range_for_expr(local_def.value),
                            )
                        }
                    }
                    _ if local_def.mutable => ExprMutability::Mutable,
                    _ => ExprMutability::ImmutableBinding(local_def.range),
                }
            }
            Expr::Param { idx, range } => {
                let param_ty = self.param_tys.as_ref().unwrap()[*idx as usize];

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
                                current_bodies!(self).range_for_expr(expr),
                            )
                        } else {
                            ExprMutability::ImmutableRef(*range)
                        }
                    }
                    _ => ExprMutability::ImmutableParam(*range, assignment),
                }
            }
            Expr::SelfGlobal(name) => {
                let fqn = hir::Fqn {
                    module: self.current_module.unwrap(),
                    name: name.name,
                };

                ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
            }
            Expr::Path { previous, field } => {
                let previous_ty = self.modules[&self.current_module.unwrap()][*previous];
                match previous_ty.as_ref() {
                    ResolvedTy::Module(module) => {
                        let fqn = hir::Fqn {
                            module: *module,
                            name: field.name,
                        };

                        if *module == self.current_module.unwrap() {
                            ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
                        } else {
                            ExprMutability::ImmutableGlobal(field.range)
                        }
                    }
                    _ if deref => {
                        let path_ty = &self.modules[&self.current_module.unwrap()][expr];

                        if path_ty
                            .as_pointer()
                            .map(|(mutable, _)| mutable)
                            .unwrap_or(true)
                        {
                            ExprMutability::Mutable
                        } else {
                            println!("here");
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
                let ty = self.modules[&self.current_module.unwrap()][expr];

                match ty.as_pointer() {
                    Some((mutable, _)) if deref => {
                        if mutable {
                            ExprMutability::Mutable
                        } else {
                            // todo: change this to be the range of the param's type
                            ExprMutability::ImmutableRef(current_bodies!(self).range_for_expr(expr))
                        }
                    }
                    Some((mutable, _)) if assignment => {
                        if mutable {
                            ExprMutability::NotMutatingRefThroughDeref(
                                current_bodies!(self).range_for_expr(expr),
                            )
                        } else {
                            ExprMutability::ImmutableRef(current_bodies!(self).range_for_expr(expr))
                        }
                    }
                    _ => ExprMutability::CannotMutate(current_bodies!(self).range_for_expr(expr)),
                }
            }
            _ => ExprMutability::CannotMutate(current_bodies!(self).range_for_expr(expr)),
        }
    }

    fn infer_stmt(&mut self, stmt: Idx<hir::Stmt>) -> Option<ResolvedTy> {
        match &current_bodies!(self)[stmt] {
            hir::Stmt::Expr(expr) => {
                self.infer_expr(*expr);

                self.find_usages(&[*expr], LocalUsage::Expr(*expr));

                None
            }
            hir::Stmt::LocalDef(local_def) => {
                let def_body = &current_bodies!(self)[*local_def];
                let value_ty = self.infer_expr(def_body.value);

                let def_ty = self.parse_expr_to_ty(def_body.ty);

                match *def_ty {
                    ResolvedTy::Unknown => {
                        // the definition does not have an annotation, so use the type of it's value
                        current_module!(self).local_tys.insert(*local_def, value_ty);
                    }
                    _ => {
                        // the definition has an annotation, so the value should match
                        if self.expect_match(value_ty, def_ty, def_body.value)
                            && self.replace_weak_tys(def_body.value, def_ty)
                        {
                            current_module!(self)
                                .expr_tys
                                .insert(def_body.value, def_ty);
                        }
                        current_module!(self).local_tys.insert(*local_def, def_ty);
                    }
                }

                self.find_usages(&[def_body.value], LocalUsage::Def(*local_def));

                None
            }
            hir::Stmt::Assign(assign) => {
                let assign_body = &current_bodies!(self)[*assign];

                let source_ty = self.infer_expr(assign_body.source);
                let value_ty = self.infer_expr(assign_body.value);

                let help = self
                    .get_mutability(assign_body.source, true, false)
                    .into_diagnostic();

                if help.is_some() {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::CannotMutate,
                        module: self.current_module.unwrap(),
                        range: assign_body.range,
                        help,
                    })
                } else if source_ty.is_weak_type_replaceable_by(&value_ty) {
                    self.replace_weak_tys(assign_body.source, source_ty);
                } else if self.expect_match(value_ty, source_ty, assign_body.value) {
                    self.replace_weak_tys(assign_body.value, source_ty);
                }

                self.find_usages(
                    &[assign_body.source, assign_body.value],
                    LocalUsage::Assign(*assign),
                );

                None
            }
        }
    }

    fn find_usages(&mut self, exprs: &[Idx<hir::Expr>], local_usage: LocalUsage) {
        let mut locals = HashSet::default();
        for expr in exprs {
            self.get_referenced_locals(*expr, &mut locals);
        }

        for local in locals {
            if let Some(usages) = current_local_usages!(self).get_mut(local) {
                usages.insert(local_usage);
            } else {
                let mut usages = FxHashSet::default();
                usages.insert(local_usage);

                current_local_usages!(self).insert(local, usages);
            }
        }
    }

    fn get_referenced_locals(&self, expr: Idx<hir::Expr>, local_defs: &mut HashSet<Idx<LocalDef>>) {
        match &current_bodies!(self)[expr] {
            Expr::Missing => {}
            Expr::IntLiteral(_) => {}
            Expr::FloatLiteral(_) => {}
            Expr::BoolLiteral(_) => {}
            Expr::StringLiteral(_) => {}
            Expr::Cast { expr, .. } => {
                self.get_referenced_locals(*expr, local_defs);
            }
            Expr::Ref { expr, .. } => {
                self.get_referenced_locals(*expr, local_defs);
            }
            Expr::Deref { pointer } => {
                self.get_referenced_locals(*pointer, local_defs);
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.get_referenced_locals(*lhs, local_defs);
                self.get_referenced_locals(*rhs, local_defs);
            }
            Expr::Unary { expr, .. } => self.get_referenced_locals(*expr, local_defs),
            Expr::Array { items, .. } => {
                for item in items {
                    self.get_referenced_locals(*item, local_defs);
                }
            }
            Expr::Index { array, index } => {
                self.get_referenced_locals(*array, local_defs);
                self.get_referenced_locals(*index, local_defs);
            }
            Expr::Block { tail_expr, .. } => {
                if let Some(tail_expr) = tail_expr {
                    self.get_referenced_locals(*tail_expr, local_defs);
                }
            }
            Expr::If {
                condition,
                body,
                else_branch,
            } => {
                self.get_referenced_locals(*condition, local_defs);
                self.get_referenced_locals(*body, local_defs);
                if let Some(else_branch) = else_branch {
                    self.get_referenced_locals(*else_branch, local_defs);
                }
            }
            Expr::While { condition, body } => {
                if let Some(condition) = condition {
                    self.get_referenced_locals(*condition, local_defs);
                }
                self.get_referenced_locals(*body, local_defs)
            }
            Expr::Local(def) => {
                local_defs.insert(*def);
            }
            Expr::SelfGlobal(_) => {}
            Expr::Param { .. } => {}
            Expr::Call { callee, args } => {
                self.get_referenced_locals(*callee, local_defs);
                for arg in args {
                    self.get_referenced_locals(*arg, local_defs);
                }
            }
            Expr::Path { previous, .. } => {
                self.get_referenced_locals(*previous, local_defs);
            }
            Expr::Lambda(_) => {}
            Expr::Comptime(_) => {}
            Expr::StructLiteral { .. } => {} // struct literals are always strongly typed
            Expr::PrimitiveTy { .. } => {}
            Expr::Import(_) => {}
        }
    }

    fn reinfer_expr(&mut self, expr: Idx<hir::Expr>) -> Intern<ResolvedTy> {
        let new_ty = match &current_bodies!(self)[expr] {
            Expr::Cast { expr: inner, .. } => {
                self.reinfer_expr(*inner);

                current_module!(self)[expr]
            }
            Expr::Ref {
                mutable,
                expr: inner,
            } => {
                let old_inner = current_module!(self)[*inner];
                let new_inner = self.reinfer_expr(*inner);

                if old_inner != new_inner {
                    ResolvedTy::Pointer {
                        mutable: *mutable,
                        sub_ty: new_inner,
                    }
                    .into()
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Deref { pointer } => {
                let old_inner = current_module!(self)[*pointer];

                let new_inner = self.reinfer_expr(*pointer);

                if old_inner != new_inner {
                    new_inner
                        .as_pointer()
                        .map(|(_, sub_ty)| sub_ty)
                        .unwrap_or_else(|| ResolvedTy::Unknown.into())
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Binary { lhs, rhs, op } => {
                let old_lhs = current_module!(self)[*lhs];
                let new_lhs = self.reinfer_expr(*lhs);

                let old_rhs = current_module!(self)[*rhs];
                let new_rhs = self.reinfer_expr(*rhs);

                if old_lhs != new_lhs || old_rhs != new_rhs {
                    if let Some(output_ty) = op.get_possible_output_ty(&new_lhs, &new_rhs) {
                        let max_ty = output_ty.max_ty.into();
                        self.replace_weak_tys(*lhs, max_ty);
                        self.replace_weak_tys(*rhs, max_ty);

                        output_ty.final_output_ty.into()
                    } else {
                        op.default_ty().into()
                    }
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Unary { expr: inner, .. } => {
                let old_inner = current_module!(self)[*inner];
                let new_inner = self.reinfer_expr(*inner);

                if old_inner != new_inner {
                    new_inner
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Array { items, .. } => {
                for item in items {
                    self.reinfer_expr(*item);
                }

                return current_module!(self)[expr];
            }
            Expr::Index { array, index } => {
                self.reinfer_expr(*index);

                let old_array = current_module!(self)[*array];
                let new_array = self.reinfer_expr(*array);

                if old_array != new_array {
                    new_array
                        .as_array()
                        .map(|(_, sub_ty)| sub_ty)
                        .unwrap_or_else(|| ResolvedTy::Unknown.into())
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => {
                let old_tail = current_module!(self)[*tail_expr];
                let new_tail = self.reinfer_expr(*tail_expr);

                if old_tail != new_tail {
                    new_tail
                } else {
                    return old_tail;
                }
            }
            Expr::Block {
                tail_expr: None, ..
            } => {
                return current_module!(self)[expr];
            }
            Expr::If {
                condition,
                body,
                else_branch,
            } => {
                self.reinfer_expr(*condition);

                let old_body = current_module!(self)[*body];
                let new_body = self.reinfer_expr(*body);

                if let Some(else_branch) = else_branch {
                    self.reinfer_expr(*else_branch);
                }

                if old_body != new_body {
                    new_body
                } else {
                    return old_body;
                }
            }
            Expr::While { condition, body } => {
                if let Some(condition) = condition {
                    self.reinfer_expr(*condition);
                }

                let old_body = current_module!(self)[*body];
                let new_body = self.reinfer_expr(*body);

                if old_body != new_body {
                    new_body
                } else {
                    return old_body;
                }
            }
            Expr::Local(local) => current_module!(self).local_tys[*local],
            _ => {
                return current_module!(self)[expr];
            }
        };

        current_module!(self).expr_tys.insert(expr, new_ty);

        new_ty
    }

    pub(crate) fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> Intern<ResolvedTy> {
        if let Some(ty) = current_module!(self).expr_tys.get(expr) {
            return *ty;
        }

        let ty = match &current_bodies!(self)[expr] {
            hir::Expr::Missing => ResolvedTy::Unknown.into(),
            hir::Expr::IntLiteral(_) => ResolvedTy::UInt(0).into(),
            hir::Expr::FloatLiteral(_) => ResolvedTy::Float(0).into(),
            hir::Expr::BoolLiteral(_) => ResolvedTy::Bool.into(),
            hir::Expr::StringLiteral(_) => ResolvedTy::String.into(),
            hir::Expr::Array { size, items, ty } => {
                let sub_ty = self.parse_expr_to_ty(*ty);

                for item in items {
                    let item_ty = self.infer_expr(*item);
                    self.expect_match(item_ty, sub_ty, *item);
                }

                ResolvedTy::Array {
                    size: size.unwrap_or(items.len() as u64),
                    sub_ty,
                }
                .into()
            }
            hir::Expr::Index { array, index } => {
                let source_ty = self.infer_expr(*array);
                // because it's annoying to do `foo^[0]`, this code lets you do `foo[0]`
                let mut deref_source_ty = source_ty;
                while let Some((_, sub_ty)) = deref_source_ty.as_pointer() {
                    deref_source_ty = sub_ty;
                }

                let index_ty = self.infer_expr(*index);

                if *deref_source_ty == ResolvedTy::Unknown {
                    ResolvedTy::Unknown.into()
                } else if let Some((actual_size, array_sub_ty)) = deref_source_ty.as_array() {
                    if let hir::Expr::IntLiteral(index) = current_bodies!(self)[*index] {
                        if index >= actual_size {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::IndexOutOfBounds {
                                    index,
                                    actual_size,
                                    array_ty: source_ty,
                                },
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });
                        }
                    }

                    if self.expect_match(index_ty, ResolvedTy::UInt(u32::MAX).into(), *index) {
                        self.replace_weak_tys(*index, ResolvedTy::UInt(u32::MAX).into());
                    }

                    array_sub_ty
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IndexNonArray { found: source_ty },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    ResolvedTy::Unknown.into()
                }
            }
            hir::Expr::Cast { expr: sub_expr, ty } => {
                let expr_ty = self.infer_expr(*sub_expr);

                if *expr_ty == ResolvedTy::Unknown {
                    ResolvedTy::Unknown.into()
                } else {
                    let cast_ty = self.parse_expr_to_ty(*ty);

                    if cast_ty.is_unknown() {
                        ResolvedTy::Unknown.into()
                    } else {
                        if !expr_ty.primitive_castable(&cast_ty) {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Uncastable {
                                    from: expr_ty,
                                    to: cast_ty,
                                },
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });
                        }

                        // replacing the existing type with the casted type
                        self.replace_weak_tys(*sub_expr, cast_ty);

                        cast_ty
                    }
                }
            }
            hir::Expr::Ref {
                mutable,
                expr: inner,
            } => {
                let inner_ty = self.infer_expr(*inner);

                if *inner_ty == ResolvedTy::Type {
                    inner_ty
                } else {
                    if *mutable {
                        let help = self.get_mutability(*inner, false, false).into_diagnostic();

                        if help.is_some() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::MutableRefToImmutableData,
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help,
                            })
                        }
                    }

                    ResolvedTy::Pointer {
                        mutable: *mutable,
                        sub_ty: inner_ty,
                    }
                    .into()
                }
            }
            hir::Expr::Deref { pointer } => {
                let deref_ty = self.infer_expr(*pointer);

                match *deref_ty {
                    ResolvedTy::Pointer { sub_ty, .. } if *sub_ty == ResolvedTy::Any => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::DerefAny,
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });

                        ResolvedTy::Unknown.into()
                    }
                    ResolvedTy::Pointer { sub_ty, .. } => sub_ty,
                    _ => {
                        if !deref_ty.is_unknown() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::DerefNonPointer { found: deref_ty },
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });
                        }

                        ResolvedTy::Unknown.into()
                    }
                }
            }
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs_ty = self.infer_expr(*lhs);
                let rhs_ty = self.infer_expr(*rhs);

                if let Some(output_ty) = op.get_possible_output_ty(&lhs_ty, &rhs_ty) {
                    if *lhs_ty != ResolvedTy::Unknown
                        && *rhs_ty != ResolvedTy::Unknown
                        && !op.can_perform(&output_ty.max_ty)
                    {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::BinaryOpMismatch {
                                op: *op,
                                first: lhs_ty,
                                second: rhs_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
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
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    op.default_ty().into()
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr_ty = self.infer_expr(*expr);

                if !op.can_perform(&expr_ty) {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::UnaryOpMismatch {
                            op: *op,
                            ty: expr_ty,
                        },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(*expr),
                        help: None,
                    });

                    op.default_ty().into()
                } else {
                    op.get_possible_output_ty(expr_ty)
                }
            }
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.infer_stmt(*stmt);
                }

                match tail_expr {
                    Some(tail) => self.infer_expr(*tail),
                    None => ResolvedTy::Void.into(),
                }
            }
            hir::Expr::If {
                condition,
                body,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(*condition);
                self.expect_match(cond_ty, ResolvedTy::Bool.into(), *condition);

                let body_ty = self.infer_expr(*body);

                if let Some(else_branch) = else_branch {
                    let else_ty = self.infer_expr(*else_branch);

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
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });

                        body_ty
                    }
                } else {
                    let help_range = match &current_bodies!(self)[*body] {
                        Expr::Block {
                            tail_expr: Some(tail_expr),
                            ..
                        } => current_bodies!(self).range_for_expr(*tail_expr),
                        _ => current_bodies!(self).range_for_expr(*body),
                    };

                    if *body_ty != ResolvedTy::Void && !body_ty.is_unknown() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MissingElse { expected: body_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: Some(TyDiagnosticHelp {
                                kind: TyDiagnosticHelpKind::IfReturnsTypeHere { found: body_ty },
                                range: help_range,
                            }),
                        });
                    }

                    body_ty
                }
            }
            hir::Expr::While { condition, body } => {
                if let Some(condition) = condition {
                    let cond_ty = self.infer_expr(*condition);
                    self.expect_match(cond_ty, ResolvedTy::Bool.into(), *condition);
                }
                let body_ty = self.infer_expr(*body);
                self.expect_match(body_ty, ResolvedTy::Void.into(), *body);

                ResolvedTy::Void.into()
            }
            hir::Expr::Local(local) => current_module!(self).local_tys[*local],
            hir::Expr::Param { idx, .. } => self.param_tys.as_ref().unwrap()[*idx as usize],
            hir::Expr::SelfGlobal(name) => {
                let fqn = hir::Fqn {
                    module: self.current_module.unwrap(),
                    name: name.name,
                };

                let definition = self.world_index.get_definition(fqn).unwrap();

                match definition {
                    hir::Definition::Global(global) => {
                        let global_signature = self.get_global_signature(global, fqn);

                        if *global_signature.ty == ResolvedTy::NotYetResolved {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::NotYetResolved {
                                    path: hir::Path::ThisModule(name.name),
                                },
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });

                            ResolvedTy::Unknown.into()
                        } else {
                            global_signature.ty
                        }
                    }
                    hir::Definition::Function(function) => {
                        let signature = self.get_function_signature(function, fqn);

                        match signature {
                            Signature::Function(fn_sig) => ResolvedTy::Function {
                                params: fn_sig.param_tys,
                                return_ty: fn_sig.return_ty,
                            }
                            .into(),
                            Signature::Global(global) => global.ty,
                        }
                    }
                }
            }
            hir::Expr::Path { previous, field } => {
                let previous_ty = self.infer_expr(*previous);
                match previous_ty.as_ref() {
                    ResolvedTy::Module(module) => {
                        let fqn = hir::Fqn {
                            module: *module,
                            name: field.name,
                        };

                        let definition = self.world_index.get_definition(fqn);

                        match definition {
                            Ok(hir::Definition::Global(global)) => {
                                let global_signature = self.get_global_signature(global, fqn);

                                if *global_signature.ty == ResolvedTy::NotYetResolved {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::NotYetResolved {
                                            path: hir::Path::OtherModule(fqn),
                                        },
                                        module: self.current_module.unwrap(),
                                        range: current_bodies!(self).range_for_expr(expr),
                                        help: None,
                                    });

                                    ResolvedTy::Unknown.into()
                                } else {
                                    global_signature.ty
                                }
                            }
                            Ok(hir::Definition::Function(function)) => {
                                let signature = self.get_function_signature(function, fqn);

                                match signature {
                                    Signature::Function(fn_sig) => ResolvedTy::Function {
                                        params: fn_sig.param_tys,
                                        return_ty: fn_sig.return_ty,
                                    }
                                    .into(),
                                    Signature::Global(global) => global.ty,
                                }
                            }
                            Err(hir::GetDefinitionError::UnknownModule) => {
                                unreachable!("a module wasn't added: {:?}", module)
                            }
                            Err(hir::GetDefinitionError::UnknownDefinition) => {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::UnknownFqn { fqn },
                                    module: self.current_module.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
                                    help: None,
                                });

                                ResolvedTy::Unknown.into()
                            }
                        }
                    }
                    _ => {
                        // because it's annoying to do `foo^.bar`, this code lets you do `foo.bar`
                        let mut deref_ty = previous_ty;
                        while let Some((_, sub_ty)) = deref_ty.as_pointer() {
                            deref_ty = sub_ty;
                        }

                        if let Some(fields) = deref_ty.as_struct() {
                            if let Some((_, ty)) =
                                fields.into_iter().find(|(name, _)| *name == field.name)
                            {
                                ty
                            } else {
                                if !previous_ty.is_unknown() {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::NonExistentField {
                                            field: field.name.0,
                                            found_ty: previous_ty,
                                        },
                                        module: self.current_module.unwrap(),
                                        range: current_bodies!(self).range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                ResolvedTy::Unknown.into()
                            }
                        } else {
                            if !previous_ty.is_unknown() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::NonExistentField {
                                        field: field.name.0,
                                        found_ty: previous_ty,
                                    },
                                    module: self.current_module.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
                                    help: None,
                                });
                            }

                            ResolvedTy::Unknown.into()
                        }
                    }
                }
            }
            hir::Expr::Call { callee, args } => {
                let callee_ty = self.infer_expr(*callee);

                if let Some((params, return_ty)) = callee_ty.clone().as_function() {
                    if params.len() != args.len() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MismatchedArgCount {
                                found: args.len(),
                                expected: params.len(),
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }

                    for (idx, arg) in args.iter().enumerate() {
                        let arg_ty = self.infer_expr(*arg);

                        if idx >= params.len() {
                            continue;
                        }
                        let param_ty = params[idx];

                        self.expect_match(arg_ty, param_ty, *arg);

                        self.replace_weak_tys(*arg, param_ty);
                    }

                    return_ty
                } else {
                    for arg in args {
                        self.infer_expr(*arg);
                    }

                    if *callee_ty != ResolvedTy::Unknown {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::CalledNonFunction { found: callee_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }

                    ResolvedTy::Unknown.into()
                }
            }
            hir::Expr::Lambda(lambda) => {
                let sig = self.generate_lambda_signature(*lambda);

                ResolvedTy::Function {
                    params: sig.param_tys,
                    return_ty: sig.return_ty,
                }
                .into()
            }
            hir::Expr::Comptime(comptime) => {
                let hir::Comptime { body } = current_bodies!(self)[*comptime];

                let ty = self.infer_expr(body);

                if ty.is_pointer() || ty.is_function() {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ComptimePointer,
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    ResolvedTy::Unknown.into()
                } else if *ty == ResolvedTy::Type {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ComptimeType,
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    ResolvedTy::Unknown.into()
                } else {
                    ty
                }
            }
            hir::Expr::StructLiteral {
                ty: ty_expr,
                fields: field_values,
            } => {
                let expected_ty = self.parse_expr_to_ty(*ty_expr);

                // IndexMap is used to make sure errors are emitted in a logical order

                let found_field_tys = field_values
                    .iter()
                    .copied()
                    .filter_map(|(name, value)| {
                        name.map(|name| (name.name, (name.range, value, self.infer_expr(value))))
                    })
                    .collect::<IndexMap<_, _>>();

                let expected_tys = match expected_ty.as_struct() {
                    Some(f) => f,
                    None => {
                        current_module!(self)
                            .expr_tys
                            .insert(expr, ResolvedTy::Unknown.into());

                        return ResolvedTy::Unknown.into();
                    }
                }
                .into_iter()
                .collect::<IndexMap<_, _>>();

                for (found_field_name, (found_field_range, found_field_expr, found_field_ty)) in
                    found_field_tys.iter()
                {
                    if let Some(expected_field_ty) = expected_tys.get(found_field_name) {
                        if self.expect_match(*found_field_ty, *expected_field_ty, *found_field_expr)
                        {
                            self.replace_weak_tys(*found_field_expr, *expected_field_ty);
                        }
                    } else {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::NonExistentField {
                                field: found_field_name.0,
                                found_ty: expected_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: *found_field_range,
                            help: None,
                        })
                    }
                }

                for expected_field_name in expected_tys.keys() {
                    if found_field_tys.get(expected_field_name).is_none() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::StructLiteralMissingField {
                                field: expected_field_name.0,
                                expected_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        })
                    }
                }

                expected_ty
            }
            hir::Expr::PrimitiveTy { .. } => ResolvedTy::Type.into(),
            Expr::Import(file_name) => ResolvedTy::Module(*file_name).into(),
        };

        current_module!(self).expr_tys.insert(expr, ty);

        ty
    }

    /// If found does not match expected, an error is thrown at the expression
    fn expect_match(
        &mut self,
        found: Intern<ResolvedTy>,
        expected: Intern<ResolvedTy>,
        expr: Idx<hir::Expr>,
    ) -> bool {
        // if the expression we're checking against is an
        // int literal (which can be inferred into any int type),
        // then we can just quickly set it's type here
        if let (
            hir::Expr::IntLiteral(num),
            ResolvedTy::IInt(bit_width) | ResolvedTy::UInt(bit_width),
        ) = (&current_bodies!(self)[expr], expected.as_ref())
        {
            if *bit_width != u32::MAX {
                current_module!(self).expr_tys[expr] = expected;
            }

            if let Some(max_size) = expected.get_max_int_size() {
                if *num > max_size {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IntTooBigForType {
                            found: *num,
                            max: max_size,
                            ty: expected,
                        },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
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
            let expr = match current_bodies!(self)[expr] {
                hir::Expr::Block {
                    tail_expr: Some(tail_expr),
                    ..
                } => tail_expr,
                _ => expr,
            };

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch { expected, found },
                module: self.current_module.unwrap(),
                range: current_bodies!(self).range_for_expr(expr),
                help: None,
            });

            false
        } else {
            true
        }
    }
}

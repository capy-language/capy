use std::collections::HashSet;

use hir::{Expr, LocalDef, TyWithRange};
use la_arena::{Arena, Idx};
use rustc_hash::FxHashSet;
use text_size::TextRange;

use crate::{
    cast::{self, TypedBinaryOp},
    InferenceCtx, LocalUsage, ResolvedTy, TyDiagnostic, TyDiagnosticHelp, TyDiagnosticHelpKind,
    TyDiagnosticKind,
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

enum ExprMutability {
    Mutable,
    ImmutableBinding(TextRange),
    ImmutableRef(TextRange),
    CannotMutate(TextRange),
}

impl InferenceCtx<'_> {
    pub(crate) fn finish_body_known(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<ResolvedTy>>,
        expected_type: ResolvedTy,
    ) {
        let actual_type = self.finish_body_unknown(body, param_tys);
        self.expect_match(actual_type, expected_type, body);
        self.replace_weak_tys(body, expected_type);
    }

    pub(crate) fn finish_body_unknown(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<ResolvedTy>>,
    ) -> ResolvedTy {
        let old_param_tys = match param_tys {
            Some(new_param_tys) => self.param_tys.replace(new_param_tys),
            None => self.param_tys.take(),
        };

        self.infer_expr(body);

        let local_usages = self.local_usages.to_owned();
        for (def, usages) in local_usages.iter() {
            self.local_usages.get_mut(def).unwrap().clear();

            println!("leftover l{} references", def.into_raw());
            self.reinfer_usages(usages.clone());
        }

        let actual_ty = self.reinfer_expr(body);

        self.param_tys = old_param_tys;

        actual_ty
    }

    fn is_weak_type_replaceable_by(&self, found: ResolvedTy, expected: ResolvedTy) -> bool {
        // println!("  is_weak_type_replaceable({:?}, {:?})", found, expected);
        match (found, expected) {
            // weak signed to strong signed, or weak unsigned to strong unsigned
            (ResolvedTy::IInt(0), ResolvedTy::IInt(bit_width))
            | (ResolvedTy::UInt(0), ResolvedTy::UInt(bit_width)) => bit_width != 0,
            // always accept a switch of sign
            (ResolvedTy::IInt(0), ResolvedTy::UInt(_))
            | (ResolvedTy::UInt(0), ResolvedTy::IInt(_)) => true,
            // always accept a switch to float
            (ResolvedTy::IInt(0) | ResolvedTy::UInt(0), ResolvedTy::Float(_)) => true,
            // weak float to strong float
            (ResolvedTy::Float(0), ResolvedTy::Float(bit_width)) => bit_width != 0,
            (
                ResolvedTy::Array {
                    size: found_size,
                    sub_ty: found_sub_ty,
                },
                ResolvedTy::Array {
                    size: expected_size,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                found_size == expected_size
                    && self.is_weak_type_replaceable_by(
                        self.resolved_arena[found_sub_ty],
                        self.resolved_arena[expected_sub_ty],
                    )
            }
            (
                ResolvedTy::Pointer {
                    mutable: found_mutable,
                    sub_ty: found_sub_ty,
                },
                ResolvedTy::Pointer {
                    mutable: expected_mutable,
                    sub_ty: expected_sub_ty,
                },
            ) => {
                matches!(
                    (found_mutable, expected_mutable),
                    (true, _) | (false, false)
                ) && self.is_weak_type_replaceable_by(
                    self.resolved_arena[found_sub_ty],
                    self.resolved_arena[expected_sub_ty],
                )
            }
            (
                ResolvedTy::Distinct { uid: found_uid, .. },
                ResolvedTy::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (found, ResolvedTy::Distinct { ty, .. }) => {
                self.is_weak_type_replaceable_by(found, self.resolved_arena[ty])
            }
            _ => false,
        }
    }

    fn get_ptr_sub_ty(resolved_arena: &Arena<ResolvedTy>, ptr: ResolvedTy) -> ResolvedTy {
        match ptr {
            ResolvedTy::Pointer { sub_ty, .. } => resolved_arena[sub_ty],
            ResolvedTy::Distinct { ty, .. } => {
                Self::get_ptr_sub_ty(resolved_arena, resolved_arena[ty])
            }
            other => panic!("did not expect to find {:?}", other),
        }
    }

    fn reinfer_usages(&mut self, usages: FxHashSet<LocalUsage>) {
        for usage in usages {
            println!("  - usage {:?}", usage);
            match usage {
                LocalUsage::Def(user_local_def) => {
                    let user_proper_ty = current_module!(self)[user_local_def];

                    let user_local_body = &current_bodies!(self)[user_local_def];

                    println!(
                        "    old ty : {:?} = {:?}",
                        user_proper_ty,
                        current_module!(self)[user_local_body.value]
                    );

                    let user_local_ty = self.reinfer_expr(user_local_body.value);

                    // if there is no type annotation on the user, then replace it's type
                    if user_local_body.ty == TyWithRange::Unknown {
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
    fn replace_weak_tys(&mut self, expr: Idx<hir::Expr>, new_ty: ResolvedTy) -> bool {
        let found_ty = current_module!(self).expr_tys[expr];

        // println!("  replace_weak_tys {:?} {:?}", found_ty, new_ty);
        if !self.is_weak_type_replaceable_by(found_ty, new_ty) {
            // println!("no");
            return false;
        }
        // println!("yeah");

        current_module!(self).expr_tys.insert(expr, new_ty);

        match current_bodies!(self)[expr] {
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
            Expr::Deref { pointer } => {
                fn get_mutable(ty: ResolvedTy, resolved_arena: &Arena<ResolvedTy>) -> bool {
                    match ty {
                        ResolvedTy::Pointer { mutable, .. } => mutable,
                        ResolvedTy::Distinct { ty, .. } => {
                            get_mutable(resolved_arena[ty], resolved_arena)
                        }
                        _ => false, // if we aren't dereferencing a pointer, there has been an error
                    }
                }

                let mutable = get_mutable(found_ty, self.resolved_arena);

                let sub_ty = self.resolved_arena.alloc(new_ty);
                self.replace_weak_tys(pointer, ResolvedTy::Pointer { mutable, sub_ty });
            }
            Expr::Ref { expr, .. } => {
                let sub_ty = Self::get_ptr_sub_ty(self.resolved_arena, new_ty);
                self.replace_weak_tys(expr, sub_ty);
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.replace_weak_tys(lhs, new_ty);
                self.replace_weak_tys(rhs, new_ty);
            }
            Expr::Unary { expr, .. } => {
                self.replace_weak_tys(expr, new_ty);
            }
            Expr::Local(local_def) => {
                println!(
                    "[START] replacing value of l{} to {:?}",
                    local_def.into_raw(),
                    new_ty
                );
                if self.replace_weak_tys(current_bodies!(self)[local_def].value, new_ty) {
                    println!("successfully replaced l{}", local_def.into_raw());
                    current_module!(self).local_tys.insert(local_def, new_ty);
                }

                println!(
                    "  new type of l{} is {:?}",
                    local_def.into_raw(),
                    current_module!(self)[local_def]
                );
                println!(
                    "  new type of #{} is {:?}",
                    current_bodies!(self)[local_def].value.into_raw(),
                    current_module!(self)[current_bodies!(self)[local_def].value]
                );

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

                println!("  [START] replacing usages");
                self.reinfer_usages(usages);
                println!("  [EXIT]");

                let local_reinferred_ty = self.reinfer_expr(current_bodies!(self)[local_def].value);

                if current_module!(self)[local_def] != local_reinferred_ty {
                    println!("not the same anymore");
                }

                println!("[EXIT]");
            }
            _ => {}
        }

        true
    }

    /// `derefs` allows certain expressions to be mutable
    /// only if they are being mutated through a deref or index
    fn get_mutability(&self, expr: Idx<Expr>, derefs: i32) -> ExprMutability {
        match &current_bodies!(self)[expr] {
            Expr::Missing => ExprMutability::Mutable,
            Expr::Array { .. } => ExprMutability::Mutable,
            Expr::Ref { mutable, .. } => {
                if *mutable && derefs > 0 {
                    ExprMutability::Mutable
                } else {
                    ExprMutability::ImmutableRef(current_bodies!(self).range_for_expr(expr))
                }
            }
            Expr::Deref { pointer } => self.get_mutability(*pointer, derefs + 1),
            Expr::Index { array, .. } => self.get_mutability(*array, derefs + 1),
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => self.get_mutability(*tail_expr, derefs),
            Expr::Local(local_def) if derefs == 0 => {
                if current_bodies!(self)[*local_def].mutable {
                    ExprMutability::Mutable
                } else {
                    ExprMutability::ImmutableBinding(current_bodies!(self)[*local_def].range)
                }
            }
            Expr::Local(local_def) if derefs > 0 => {
                let local_def = &current_bodies!(self)[*local_def];

                self.get_mutability(local_def.value, derefs)
            }
            Expr::Call { .. } if derefs > 0 => ExprMutability::Mutable,
            Expr::Param { idx } => {
                let param_ty = self.param_tys.as_ref().unwrap()[*idx as usize];

                if derefs > 0 {
                    if let Some((mutable, _)) = param_ty.get_pointer_semantics(self.resolved_arena)
                    {
                        if mutable {
                            ExprMutability::Mutable
                        } else {
                            ExprMutability::ImmutableRef(current_bodies!(self).range_for_expr(expr))
                        }
                    } else if param_ty.is_array(self.resolved_arena) {
                        ExprMutability::Mutable // todo: i don't like this, the parameter itself should be `mut`
                    } else {
                        unreachable!("Only pointers and arrays can be dereferenced")
                    }
                } else {
                    // todo: for these, the param itself should be declared as `mut`
                    ExprMutability::CannotMutate(current_bodies!(self).range_for_expr(expr))
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

                let def_ty = self.resolve_ty(def_body.ty);

                match &def_ty {
                    ResolvedTy::Unknown => {
                        // the definition does not have an annotation, so use the type of it's value
                        current_module!(self).local_tys.insert(*local_def, value_ty);
                    }
                    def_ty => {
                        // the definition has an annotation, so the value should match
                        if self.expect_match(value_ty, *def_ty, def_body.value)
                            && self.replace_weak_tys(def_body.value, *def_ty)
                        {
                            current_module!(self)
                                .expr_tys
                                .insert(def_body.value, *def_ty);
                        }
                        current_module!(self).local_tys.insert(*local_def, *def_ty);
                    }
                }

                self.find_usages(&[def_body.value], LocalUsage::Def(*local_def));

                None
            }
            hir::Stmt::Assign(assign) => {
                let assign_body = &current_bodies!(self)[*assign];

                match &current_bodies!(self)[assign_body.source] {
                    Expr::Missing => {}
                    Expr::Deref { .. } | Expr::Index { .. } | Expr::Local(_) => {
                        let help = match self.get_mutability(assign_body.source, 0) {
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
                            ExprMutability::Mutable => None,
                        };

                        if help.is_some() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::CannotMutate,
                                module: self.current_module.unwrap(),
                                range: assign_body.range,
                                help,
                            })
                        }
                    }
                    // Expr::Global(_) => {}, assignment to globals isn't allowed
                    // Expr::Param { idx } => {}, assignment to parameters isn't allowed
                    _ => self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::CannotMutate,
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(assign_body.source),
                        help: None,
                    }),
                }

                let source_ty = self.infer_expr(assign_body.source);
                let value_ty = self.infer_expr(assign_body.value);

                self.expect_match(value_ty, source_ty, assign_body.value);

                self.replace_weak_tys(assign_body.value, source_ty);

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
            println!("reference to l{} in {:?}", local.into_raw(), local_usage);
            if let Some(usages) = self.local_usages.get_mut(local) {
                usages.insert(local_usage);
            } else {
                let mut usages = FxHashSet::default();
                usages.insert(local_usage);

                self.local_usages.insert(local, usages);
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
                self.get_referenced_locals(*index, local_defs);
                self.get_referenced_locals(*array, local_defs);
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
            Expr::Global(_) => {}
            Expr::Param { .. } => {}
            Expr::Call { args, .. } => {
                for arg in args {
                    self.get_referenced_locals(*arg, local_defs);
                }
            }
            Expr::PrimitiveTy { .. } => {}
        }
    }

    fn reinfer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
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
                        sub_ty: self.resolved_arena.alloc(new_inner),
                    }
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Deref { pointer } => {
                let old_inner = current_module!(self)[*pointer];

                let new_inner = self.reinfer_expr(*pointer);

                if old_inner != new_inner {
                    match new_inner {
                        ResolvedTy::Pointer { sub_ty, .. } => self.resolved_arena[sub_ty],
                        _ => ResolvedTy::Unknown,
                    }
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
                    if let Some(output_ty) =
                        op.get_possible_output_ty(self.resolved_arena, new_lhs, new_rhs)
                    {
                        self.replace_weak_tys(*lhs, output_ty.max_ty);
                        self.replace_weak_tys(*rhs, output_ty.max_ty);

                        output_ty.final_output_ty
                    } else {
                        op.default_ty()
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
                        .get_array_semantics(self.resolved_arena)
                        .map(|(_, sub_ty)| sub_ty)
                        .unwrap_or(ResolvedTy::Unknown)
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
                    println!("reinfer condition");
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
            _ => return current_module!(self)[expr],
        };

        current_module!(self).expr_tys.insert(expr, new_ty);

        new_ty
    }

    fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
        if current_module!(self).expr_tys.get(expr).is_some() {
            return self.reinfer_expr(expr);
        }

        let ty = match &current_bodies!(self)[expr] {
            hir::Expr::Missing => ResolvedTy::Unknown,
            hir::Expr::IntLiteral(_) => ResolvedTy::UInt(0),
            hir::Expr::FloatLiteral(_) => ResolvedTy::Float(0),
            hir::Expr::BoolLiteral(_) => ResolvedTy::Bool,
            hir::Expr::StringLiteral(_) => ResolvedTy::String,
            hir::Expr::Array { size, items, ty } => {
                let sub_ty = self.resolve_ty(*ty);

                for item in items {
                    let item_ty = self.infer_expr(*item);
                    self.expect_match(item_ty, sub_ty, *item);
                }

                ResolvedTy::Array {
                    size: size.unwrap_or(items.len() as u64),
                    sub_ty: self.resolved_arena.alloc(sub_ty),
                }
            }
            hir::Expr::Index { array, index } => {
                let source_ty = self.infer_expr(*array);

                if source_ty == ResolvedTy::Unknown {
                    ResolvedTy::Unknown
                } else if let Some((actual_size, array_sub_ty)) =
                    source_ty.get_array_semantics(self.resolved_arena)
                {
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

                    let index_ty = self.infer_expr(*index);

                    if self.expect_match(index_ty, ResolvedTy::UInt(u32::MAX), *index) {
                        self.replace_weak_tys(*index, ResolvedTy::UInt(u32::MAX));
                    }

                    array_sub_ty
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IndexMismatch { found: source_ty },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    ResolvedTy::Unknown
                }
            }
            hir::Expr::Cast { expr: sub_expr, ty } => {
                let expr_ty = self.infer_expr(*sub_expr);

                if expr_ty == ResolvedTy::Unknown {
                    ResolvedTy::Unknown
                } else {
                    match ty {
                        TyWithRange::Unknown => expr_ty,
                        _ => {
                            let cast_ty = self.resolve_ty(*ty);

                            if !cast::primitive_castable(self.resolved_arena, expr_ty, cast_ty) {
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
            }
            hir::Expr::Ref {
                mutable,
                expr: sub_expr,
            } => {
                if *mutable {
                    let help = match self.get_mutability(*sub_expr, 0) {
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
                        ExprMutability::Mutable => None,
                    };

                    if help.is_some() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MutableRefToImmutableData,
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help,
                        })
                    }
                }

                let sub_ty = self.infer_expr(*sub_expr);

                if matches!(sub_ty, ResolvedTy::Type) {
                    ResolvedTy::Type
                } else {
                    ResolvedTy::Pointer {
                        mutable: *mutable,
                        sub_ty: self.resolved_arena.alloc(sub_ty),
                    }
                }
            }
            hir::Expr::Deref { pointer } => {
                let deref_ty = self.infer_expr(*pointer);

                match deref_ty {
                    ResolvedTy::Pointer { sub_ty, .. } => self.resolved_arena[sub_ty],
                    _ => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::DerefMismatch { found: deref_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });

                        ResolvedTy::Unknown
                    }
                }
            }
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs_ty = self.infer_expr(*lhs);
                let rhs_ty = self.infer_expr(*rhs);

                if let Some(output_ty) =
                    op.get_possible_output_ty(self.resolved_arena, lhs_ty, rhs_ty)
                {
                    if lhs_ty != ResolvedTy::Unknown
                        && rhs_ty != ResolvedTy::Unknown
                        && !op.can_perform(self.resolved_arena, output_ty.max_ty)
                    {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::OpMismatch {
                                op: *op,
                                first: lhs_ty,
                                second: rhs_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }

                    self.replace_weak_tys(*lhs, output_ty.max_ty);
                    self.replace_weak_tys(*rhs, output_ty.max_ty);

                    output_ty.final_output_ty
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::OpMismatch {
                            op: *op,
                            first: lhs_ty,
                            second: rhs_ty,
                        },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    op.default_ty()
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr_type = self.infer_expr(*expr);

                match op {
                    hir::UnaryOp::Neg => {
                        self.expect_match(expr_type, ResolvedTy::IInt(0), *expr);
                        match expr_type {
                            ResolvedTy::UInt(bit_width) | ResolvedTy::IInt(bit_width) => {
                                ResolvedTy::IInt(bit_width)
                            }
                            _ => ResolvedTy::Unknown,
                        }
                    }
                    hir::UnaryOp::Not => {
                        self.expect_match(expr_type, ResolvedTy::Bool, *expr);
                        expr_type
                    }
                    hir::UnaryOp::Pos => {
                        self.expect_match(expr_type, ResolvedTy::IInt(0), *expr);
                        expr_type
                    }
                }
            }
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.infer_stmt(*stmt);
                }

                match tail_expr {
                    Some(tail) => self.infer_expr(*tail),
                    None => ResolvedTy::Void,
                }
            }
            hir::Expr::If {
                condition,
                body,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(*condition);
                self.expect_match(cond_ty, ResolvedTy::Bool, *condition);

                let body_ty = self.infer_expr(*body);

                if let Some(else_branch) = else_branch {
                    let else_ty = self.infer_expr(*else_branch);

                    if let Some(real_ty) = cast::max_cast(self.resolved_arena, body_ty, else_ty) {
                        self.replace_weak_tys(*body, real_ty);
                        self.replace_weak_tys(*else_branch, real_ty);
                        real_ty
                    } else {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IfMismatch {
                                found: body_ty,
                                expected: else_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });

                        body_ty
                    }
                } else {
                    if !matches!(body_ty, ResolvedTy::Unknown | ResolvedTy::Void) {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MissingElse { expected: body_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }

                    body_ty
                }
            }
            hir::Expr::While { condition, body } => {
                if let Some(condition) = condition {
                    let _ = self.infer_expr(*condition);
                }
                let body_ty = self.infer_expr(*body);
                self.expect_match(body_ty, ResolvedTy::Void, *body);

                ResolvedTy::Void
            }
            hir::Expr::Local(local) => current_module!(self).local_tys[*local],
            hir::Expr::Param { idx } => self.param_tys.as_ref().unwrap()[*idx as usize],
            hir::Expr::Call { path, args } => {
                let fqn = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn {
                        module: self.current_module.unwrap(),
                        name,
                    },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let definition = self.world_index.get_definition(fqn).unwrap();

                let function = match definition {
                    hir::Definition::Function(f) => f,
                    _ => todo!(),
                };

                let function_signature = self.singleton_fn_signature(function, fqn);

                for (idx, arg) in args.iter().enumerate() {
                    let arg_ty = self.infer_expr(*arg);
                    let param_ty = function_signature.param_tys[idx];
                    self.expect_match(arg_ty, param_ty, *arg);

                    self.replace_weak_tys(*arg, param_ty);
                }

                function_signature.return_ty
            }
            hir::Expr::Global(path) => {
                let fqn = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn {
                        module: self.current_module.unwrap(),
                        name,
                    },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let definition = self.world_index.get_definition(fqn).unwrap();

                let global = match definition {
                    hir::Definition::Global(global) => global,
                    _ => todo!(),
                };

                let global_signature = self.singleton_global_signature(global, fqn);

                if global_signature.ty == ResolvedTy::NotYetResolved {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::NotYetResolved { path: path.path() },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    ResolvedTy::Unknown
                } else {
                    global_signature.ty
                }
            }
            hir::Expr::PrimitiveTy { .. } => ResolvedTy::Type,
        };

        current_module!(self).expr_tys.insert(expr, ty);

        ty
    }

    fn expect_match(
        &mut self,
        found: ResolvedTy,
        expected: ResolvedTy,
        expr: Idx<hir::Expr>,
    ) -> bool {
        // if the expression we're checking against is an
        // int literal (which can be inferred into any int type),
        // then we can just quickly set it's type here
        if let (
            hir::Expr::IntLiteral(_),
            ResolvedTy::IInt(bit_width) | ResolvedTy::UInt(bit_width),
        ) = (&current_bodies!(self)[expr], expected)
        {
            if bit_width != u32::MAX {
                current_module!(self).expr_tys[expr] = expected;
            }
            return true;
        }

        if found.is_unknown(self.resolved_arena) || expected.is_unknown(self.resolved_arena) {
            // return false without throwing an error
            return false;
        }

        if !cast::can_fit(self.resolved_arena, found, expected) {
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

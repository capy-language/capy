use std::collections::HashSet;

use hir::{Expr, LocalDef, TyWithRange};
use la_arena::Idx;
use rustc_hash::FxHashSet;
use text_size::TextRange;

use crate::{
    resolved_ty::TypedBinaryOp, InferenceCtx, LocalUsage, ResolvedTy, Signature, TyDiagnostic,
    TyDiagnosticHelp, TyDiagnosticHelpKind, TyDiagnosticKind,
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
        match $self.local_usages.get_mut(&$self.current_module.unwrap()) {
            Some(usages) => usages,
            None => {
                $self
                    .local_usages
                    .insert($self.current_module.unwrap(), la_arena::ArenaMap::default());

                $self
                    .local_usages
                    .get_mut(&$self.current_module.unwrap())
                    .unwrap()
            }
        }
    };
}

enum ExprMutability {
    Mutable,
    ImmutableBinding(TextRange),
    ImmutableRef(TextRange),
    ImmutableParam(TextRange),
    ImmutableGlobal(TextRange),
    CannotMutate(TextRange),
}

impl InferenceCtx<'_> {
    pub(crate) fn finish_body_known(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<Idx<ResolvedTy>>>,
        expected_ty: ResolvedTy,
    ) {
        let actual_type = self.finish_body_unknown(body, param_tys);
        self.expect_match(&actual_type, &expected_ty, body);
        self.replace_weak_tys(body, &expected_ty);
    }

    pub(crate) fn finish_body_unknown(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<Idx<ResolvedTy>>>,
    ) -> ResolvedTy {
        let old_param_tys = match param_tys {
            Some(new_param_tys) => self.param_tys.replace(new_param_tys),
            None => self.param_tys.take(),
        };

        self.infer_expr(body);

        let local_usages = current_local_usages!(self).clone();
        for (def, usages) in local_usages.iter() {
            current_local_usages!(self).get_mut(def).unwrap().clear();

            // println!("leftover l{} references", def.into_raw());
            self.reinfer_usages(usages.clone());
        }

        let actual_ty = self.reinfer_expr(body);

        self.param_tys = old_param_tys;

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
    fn replace_weak_tys(&mut self, expr: Idx<hir::Expr>, new_ty: &ResolvedTy) -> bool {
        let found_ty = &current_module!(self).expr_tys[expr];

        // println!("  replace_weak_tys {:?} {:?}", found_ty, new_ty);
        if !found_ty.is_weak_type_replaceable_by(new_ty, self.resolved_arena) {
            // println!("no");
            return false;
        }
        // println!("yeah");

        current_module!(self).expr_tys.insert(expr, new_ty.clone());

        match current_bodies!(self)[expr].clone() {
            Expr::IntLiteral(num) => {
                if let Some(max_size) = new_ty.get_max_int_size(self.resolved_arena) {
                    if num > max_size {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IntTooBigForType {
                                found: num,
                                max: max_size,
                                ty: new_ty.clone(),
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
            Expr::Deref { pointer } => {
                let mutable = current_module!(self).expr_tys[expr]
                    .as_pointer(self.resolved_arena)
                    .map(|(mutable, _)| mutable)
                    .unwrap_or_default();

                let sub_ty = self.resolved_arena.alloc(new_ty.clone());
                self.replace_weak_tys(pointer, &ResolvedTy::Pointer { mutable, sub_ty });
            }
            Expr::Ref { expr, .. } => {
                if let Some(sub_ty) = new_ty
                    .as_pointer(self.resolved_arena)
                    .map(|(_, sub_ty)| self.resolved_arena[sub_ty].clone())
                {
                    self.replace_weak_tys(expr, &sub_ty);
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
                    current_module!(self)
                        .local_tys
                        .insert(local_def, new_ty.clone());
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
                let field_tys = new_ty.as_struct(self.resolved_arena).unwrap();

                for (idx, (_, value)) in fields.into_iter().enumerate() {
                    let new_field_ty = field_tys[idx].1;
                    let new_field_ty = self.resolved_arena[new_field_ty].clone();

                    self.replace_weak_tys(value, &new_field_ty);
                }
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
            Expr::Param { idx } => {
                let param_ty = self.param_tys.as_ref().unwrap()[*idx as usize];
                let param_ty = &self.resolved_arena[param_ty];

                if derefs > 0 {
                    if let Some((mutable, _)) = param_ty.as_pointer(self.resolved_arena) {
                        if mutable {
                            ExprMutability::Mutable
                        } else {
                            ExprMutability::ImmutableRef(current_bodies!(self).range_for_expr(expr))
                        }
                    } else {
                        ExprMutability::ImmutableParam(current_bodies!(self).range_for_expr(expr))
                    }
                } else {
                    ExprMutability::ImmutableParam(current_bodies!(self).range_for_expr(expr))
                }
            }
            Expr::Global(_) => {
                ExprMutability::ImmutableGlobal(current_bodies!(self).range_for_expr(expr))
            }
            Expr::Path { previous, .. } => self.get_mutability(*previous, derefs),
            Expr::Call { .. } if derefs > 0 => ExprMutability::Mutable,
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

                match &def_ty {
                    ResolvedTy::Unknown => {
                        // the definition does not have an annotation, so use the type of it's value
                        current_module!(self).local_tys.insert(*local_def, value_ty);
                    }
                    def_ty => {
                        // the definition has an annotation, so the value should match
                        if self.expect_match(&value_ty, def_ty, def_body.value)
                            && self.replace_weak_tys(def_body.value, def_ty)
                        {
                            current_module!(self)
                                .expr_tys
                                .insert(def_body.value, def_ty.clone());
                        }
                        current_module!(self)
                            .local_tys
                            .insert(*local_def, def_ty.clone());
                    }
                }

                self.find_usages(&[def_body.value], LocalUsage::Def(*local_def));

                None
            }
            hir::Stmt::Assign(assign) => {
                let assign_body = &current_bodies!(self)[*assign];

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
                    ExprMutability::ImmutableParam(range) => Some(TyDiagnosticHelp {
                        kind: TyDiagnosticHelpKind::ImmutableParam,
                        range,
                    }),
                    ExprMutability::ImmutableGlobal(range) => Some(TyDiagnosticHelp {
                        kind: TyDiagnosticHelpKind::ImmutableGlobal,
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

                let source_ty = self.infer_expr(assign_body.source);
                let value_ty = self.infer_expr(assign_body.value);

                self.expect_match(&value_ty, &source_ty, assign_body.value);

                self.replace_weak_tys(assign_body.value, &source_ty);

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
            // println!("reference to l{} in {:?}", local.into_raw(), local_usage);
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
            Expr::Global(_) => {}
            Expr::Param { .. } => {}
            Expr::Call { callee, args } => {
                self.get_referenced_locals(*callee, local_defs);
                for arg in args {
                    self.get_referenced_locals(*arg, local_defs);
                }
            }
            Expr::Module(_) => {}
            Expr::Path { previous, .. } => {
                self.get_referenced_locals(*previous, local_defs);
            }
            Expr::Lambda(_) => {}
            Expr::StructLiteral { .. } => {} // struct literals are always strongly typed
            Expr::PrimitiveTy { .. } => {}
        }
    }

    fn reinfer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
        let new_ty = match &current_bodies!(self)[expr] {
            Expr::Cast { expr: inner, .. } => {
                self.reinfer_expr(*inner);

                current_module!(self)[expr].clone()
            }
            Expr::Ref {
                mutable,
                expr: inner,
            } => {
                let old_inner = current_module!(self)[*inner].clone();
                let new_inner = self.reinfer_expr(*inner);

                if old_inner != new_inner {
                    ResolvedTy::Pointer {
                        mutable: *mutable,
                        sub_ty: self.resolved_arena.alloc(new_inner),
                    }
                } else {
                    return current_module!(self)[expr].clone();
                }
            }
            Expr::Deref { pointer } => {
                let old_inner = current_module!(self)[*pointer].clone();

                let new_inner = self.reinfer_expr(*pointer);

                if old_inner != new_inner {
                    match new_inner {
                        ResolvedTy::Pointer { sub_ty, .. } => self.resolved_arena[sub_ty].clone(),
                        _ => ResolvedTy::Unknown,
                    }
                } else {
                    return current_module!(self)[expr].clone();
                }
            }
            Expr::Binary { lhs, rhs, op } => {
                let old_lhs = current_module!(self)[*lhs].clone();
                let new_lhs = self.reinfer_expr(*lhs);

                let old_rhs = current_module!(self)[*rhs].clone();
                let new_rhs = self.reinfer_expr(*rhs);

                if old_lhs != new_lhs || old_rhs != new_rhs {
                    if let Some(output_ty) =
                        op.get_possible_output_ty(self.resolved_arena, &new_lhs, &new_rhs)
                    {
                        self.replace_weak_tys(*lhs, &output_ty.max_ty);
                        self.replace_weak_tys(*rhs, &output_ty.max_ty);

                        output_ty.final_output_ty
                    } else {
                        op.default_ty()
                    }
                } else {
                    return current_module!(self)[expr].clone();
                }
            }
            Expr::Unary { expr: inner, .. } => {
                let old_inner = current_module!(self)[*inner].clone();
                let new_inner = self.reinfer_expr(*inner);

                if old_inner != new_inner {
                    new_inner
                } else {
                    return current_module!(self)[expr].clone();
                }
            }
            Expr::Array { items, .. } => {
                for item in items {
                    self.reinfer_expr(*item);
                }

                return current_module!(self)[expr].clone();
            }
            Expr::Index { array, index } => {
                println!(
                    "#{} is {:?}",
                    array.into_raw(),
                    current_module!(self)[*array]
                );
                self.reinfer_expr(*index);

                let old_array = current_module!(self)[*array].clone();
                let new_array = self.reinfer_expr(*array);

                if old_array != new_array {
                    new_array
                        .as_array(self.resolved_arena)
                        .map(|(_, sub_ty)| self.resolved_arena[sub_ty].clone())
                        .unwrap_or(ResolvedTy::Unknown)
                } else {
                    return current_module!(self)[expr].clone();
                }
            }
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => {
                let old_tail = current_module!(self)[*tail_expr].clone();
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
                return current_module!(self)[expr].clone();
            }
            Expr::If {
                condition,
                body,
                else_branch,
            } => {
                self.reinfer_expr(*condition);

                let old_body = current_module!(self)[*body].clone();
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

                let old_body = current_module!(self)[*body].clone();
                let new_body = self.reinfer_expr(*body);

                if old_body != new_body {
                    new_body
                } else {
                    return old_body;
                }
            }
            Expr::Local(local) => current_module!(self).local_tys[*local].clone(),
            _ => {
                println!("#{}", expr.into_raw());
                return current_module!(self)[expr].clone();
            }
        };

        current_module!(self).expr_tys.insert(expr, new_ty.clone());

        new_ty
    }

    pub(crate) fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
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
                    self.expect_match(&item_ty, &sub_ty, *item);
                }

                ResolvedTy::Array {
                    size: size.unwrap_or(items.len() as u64),
                    sub_ty: self.resolved_arena.alloc(sub_ty),
                }
            }
            hir::Expr::Index { array, index } => {
                let source_ty = self.infer_expr(*array);
                let index_ty = self.infer_expr(*index);

                println!(
                    "#{} is {:?}",
                    array.into_raw(),
                    current_module!(self)[*array]
                );

                if source_ty == ResolvedTy::Unknown {
                    ResolvedTy::Unknown
                } else if let Some((actual_size, array_sub_ty)) =
                    source_ty.clone().as_array(self.resolved_arena)
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

                    if self.expect_match(&index_ty, &ResolvedTy::UInt(u32::MAX), *index) {
                        self.replace_weak_tys(*index, &ResolvedTy::UInt(u32::MAX));
                    }

                    self.resolved_arena[array_sub_ty].clone()
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IndexNonArray { found: source_ty },
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
                    match self.twr_arena[*ty] {
                        TyWithRange::Unknown => expr_ty,
                        _ => {
                            let cast_ty = self.resolve_ty(*ty);

                            if !expr_ty.primitive_castable(&cast_ty, self.resolved_arena) {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::Uncastable {
                                        from: expr_ty,
                                        to: cast_ty.clone(),
                                    },
                                    module: self.current_module.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
                                    help: None,
                                });
                            }

                            // replacing the existing type with the casted type
                            self.replace_weak_tys(*sub_expr, &cast_ty);

                            cast_ty
                        }
                    }
                }
            }
            hir::Expr::Ref {
                mutable,
                expr: sub_expr,
            } => {
                let sub_ty = self.infer_expr(*sub_expr);

                if matches!(sub_ty, ResolvedTy::Type) {
                    ResolvedTy::Type
                } else {
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
                            ExprMutability::ImmutableParam(range) => Some(TyDiagnosticHelp {
                                kind: TyDiagnosticHelpKind::ImmutableParam,
                                range,
                            }),
                            ExprMutability::ImmutableGlobal(range) => Some(TyDiagnosticHelp {
                                kind: TyDiagnosticHelpKind::ImmutableGlobal,
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

                    ResolvedTy::Pointer {
                        mutable: *mutable,
                        sub_ty: self.resolved_arena.alloc(sub_ty),
                    }
                }
            }
            hir::Expr::Deref { pointer } => {
                let deref_ty = self.infer_expr(*pointer);

                match deref_ty {
                    ResolvedTy::Pointer { sub_ty, .. } => self.resolved_arena[sub_ty].clone(),
                    _ => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::DerefNonPointer { found: deref_ty },
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
                    op.get_possible_output_ty(self.resolved_arena, &lhs_ty, &rhs_ty)
                {
                    if lhs_ty != ResolvedTy::Unknown
                        && rhs_ty != ResolvedTy::Unknown
                        && !op.can_perform(self.resolved_arena, &output_ty.max_ty)
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

                    self.replace_weak_tys(*lhs, &output_ty.max_ty);
                    self.replace_weak_tys(*rhs, &output_ty.max_ty);

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
                let expr_ty = self.infer_expr(*expr);

                match op {
                    hir::UnaryOp::Neg => {
                        self.expect_match(&expr_ty, &ResolvedTy::IInt(0), *expr);
                        match expr_ty {
                            ResolvedTy::UInt(bit_width) | ResolvedTy::IInt(bit_width) => {
                                ResolvedTy::IInt(bit_width)
                            }
                            _ => ResolvedTy::Unknown,
                        }
                    }
                    hir::UnaryOp::Not => {
                        self.expect_match(&expr_ty, &ResolvedTy::Bool, *expr);
                        expr_ty
                    }
                    hir::UnaryOp::Pos => {
                        self.expect_match(&expr_ty, &ResolvedTy::IInt(0), *expr);
                        expr_ty
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
                self.expect_match(&cond_ty, &ResolvedTy::Bool, *condition);

                let body_ty = self.infer_expr(*body);

                if let Some(else_branch) = else_branch {
                    let else_ty = self.infer_expr(*else_branch);

                    if let Some(real_ty) = body_ty.max(&else_ty, self.resolved_arena) {
                        self.replace_weak_tys(*body, &real_ty);
                        self.replace_weak_tys(*else_branch, &real_ty);
                        real_ty
                    } else {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IfMismatch {
                                found: else_ty,
                                expected: body_ty.clone(),
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
                        // this *should* be unreachable
                        _ => current_bodies!(self).range_for_expr(*body),
                    };

                    if !matches!(body_ty, ResolvedTy::Unknown | ResolvedTy::Void) {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MissingElse {
                                expected: body_ty.clone(),
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: Some(TyDiagnosticHelp {
                                kind: TyDiagnosticHelpKind::IfReturnsTypeHere {
                                    found: body_ty.clone(),
                                },
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
                    self.expect_match(&cond_ty, &ResolvedTy::Bool, *condition);
                }
                let body_ty = self.infer_expr(*body);
                self.expect_match(&body_ty, &ResolvedTy::Void, *body);

                ResolvedTy::Void
            }
            hir::Expr::Local(local) => current_module!(self).local_tys[*local].clone(),
            hir::Expr::Param { idx } => {
                self.resolved_arena[self.param_tys.as_ref().unwrap()[*idx as usize]].clone()
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

                match definition {
                    hir::Definition::Global(global) => {
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
                    hir::Definition::Function(function) => {
                        let signature = self.get_function_signature(function, fqn);

                        match signature {
                            Signature::Function(fn_sig) => ResolvedTy::Function {
                                params: fn_sig.param_tys,
                                // todo: I don't like this alloc
                                return_ty: self.resolved_arena.alloc(fn_sig.return_ty),
                            },
                            Signature::Global(global) => global.ty,
                        }
                    }
                }
            }
            hir::Expr::Module(_) => {
                panic!("modules can't be referred to just as themselves");
            }
            hir::Expr::Path {
                previous, field, ..
            } => match &current_bodies!(self)[*previous] {
                hir::Expr::Module(module_name) => {
                    let fqn = hir::Fqn {
                        module: *module_name,
                        name: *field,
                    };

                    let definition = self.world_index.get_definition(fqn);

                    match definition {
                        Ok(hir::Definition::Global(global)) => {
                            let global_signature = self.singleton_global_signature(global, fqn);

                            if global_signature.ty == ResolvedTy::NotYetResolved {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::NotYetResolved {
                                        path: hir::Path::OtherModule(fqn),
                                    },
                                    module: self.current_module.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
                                    help: None,
                                });

                                ResolvedTy::Unknown
                            } else {
                                global_signature.ty
                            }
                        }
                        Ok(hir::Definition::Function(function)) => {
                            let signature = self.get_function_signature(function, fqn);

                            match signature {
                                Signature::Function(fn_sig) => ResolvedTy::Function {
                                    params: fn_sig.param_tys,
                                    return_ty: self.resolved_arena.alloc(fn_sig.return_ty),
                                },
                                Signature::Global(global) => global.ty,
                            }
                        }
                        Err(hir::GetDefinitionError::UnknownModule) => unreachable!(),
                        Err(hir::GetDefinitionError::UnknownDefinition) => {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::UnknownFqn { fqn },
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });

                            ResolvedTy::Unknown
                        }
                    }
                }
                _ => {
                    let previous_ty = self.infer_expr(*previous);

                    if let Some(fields) = previous_ty.as_struct(self.resolved_arena) {
                        if let Some((_, ty)) = fields.iter().find(|(name, _)| name == &Some(*field))
                        {
                            self.resolved_arena[*ty].clone()
                        } else {
                            if !previous_ty.is_unknown(self.resolved_arena) {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::NonExistentField {
                                        field: field.0,
                                        found: previous_ty,
                                    },
                                    module: self.current_module.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
                                    help: None,
                                });
                            }

                            ResolvedTy::Unknown
                        }
                    } else {
                        let previous_ty = self.infer_expr(*previous);

                        if !previous_ty.is_unknown(self.resolved_arena) {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::NonExistentField {
                                    field: field.0,
                                    found: previous_ty,
                                },
                                module: self.current_module.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });
                        }

                        ResolvedTy::Unknown
                    }
                }
            },
            hir::Expr::Call { callee, args } => {
                let callee_ty = self.infer_expr(*callee);

                if let Some((params, return_ty)) =
                    callee_ty.clone().as_function(self.resolved_arena)
                {
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
                        let param_ty = &self.resolved_arena[params[idx]].clone();

                        self.expect_match(&arg_ty, param_ty, *arg);

                        self.replace_weak_tys(*arg, param_ty);
                    }

                    self.resolved_arena[return_ty].clone()
                } else {
                    for arg in args {
                        self.infer_expr(*arg);
                    }

                    if callee_ty != ResolvedTy::Unknown {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::CalledNonFunction { found: callee_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }

                    ResolvedTy::Unknown
                }
            }
            hir::Expr::Lambda(lambda) => {
                let sig = self.generate_unnamed_function_signature(*lambda);

                ResolvedTy::Function {
                    params: sig.param_tys,
                    return_ty: self.resolved_arena.alloc(sig.return_ty),
                }
            }
            hir::Expr::StructLiteral {
                ty: ty_expr,
                fields: field_values,
            } => {
                let ty = self.parse_expr_to_ty(*ty_expr);

                let field_tys = field_values
                    .iter()
                    .copied()
                    .map(|(name, value)| {
                        let value_ty = self.infer_expr(value);
                        (name, self.resolved_arena.alloc(value_ty))
                    })
                    .collect::<Vec<_>>();

                let actual_ty = ResolvedTy::Struct { fields: field_tys };

                if self.expect_match(&actual_ty, &ty, expr) {
                    let expected_field_tys = ty.as_struct(self.resolved_arena).unwrap();

                    for (idx, (_, field_val)) in field_values.iter().enumerate() {
                        let expected_field_ty =
                            self.resolved_arena[expected_field_tys[idx].1].clone();
                        self.replace_weak_tys(*field_val, &expected_field_ty);
                    }

                    ty
                } else {
                    actual_ty
                }
            }
            hir::Expr::PrimitiveTy { .. } => ResolvedTy::Type,
        };

        current_module!(self).expr_tys.insert(expr, ty.clone());

        ty
    }

    /// If found does not match expected, an error is thrown at the expression
    fn expect_match(
        &mut self,
        found: &ResolvedTy,
        expected: &ResolvedTy,
        expr: Idx<hir::Expr>,
    ) -> bool {
        // if the expression we're checking against is an
        // int literal (which can be inferred into any int type),
        // then we can just quickly set it's type here
        if let (
            hir::Expr::IntLiteral(num),
            ResolvedTy::IInt(bit_width) | ResolvedTy::UInt(bit_width),
        ) = (&current_bodies!(self)[expr], expected)
        {
            if *bit_width != u32::MAX {
                current_module!(self).expr_tys[expr] = expected.clone();
            }

            if let Some(max_size) = expected.get_max_int_size(self.resolved_arena) {
                if *num > max_size {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IntTooBigForType {
                            found: *num,
                            max: max_size,
                            ty: expected.clone(),
                        },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });
                }
            }

            return true;
        }

        if found.is_unknown(self.resolved_arena) || expected.is_unknown(self.resolved_arena) {
            // return false without throwing an error
            return false;
        }

        if !found.can_fit_into(expected, self.resolved_arena) {
            let expr = match current_bodies!(self)[expr] {
                hir::Expr::Block {
                    tail_expr: Some(tail_expr),
                    ..
                } => tail_expr,
                _ => expr,
            };

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch {
                    expected: expected.clone(),
                    found: found.clone(),
                },
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

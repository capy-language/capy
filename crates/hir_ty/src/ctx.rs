use std::collections::HashSet;

use hir::{Expr, LocalDef};
use indexmap::IndexMap;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashSet;
use text_size::TextRange;

use crate::{
    resolved_ty::BinaryOutput, InferenceCtx, LocalUsage, Ty, TyDiagnostic, TyDiagnosticHelp,
    TyDiagnosticHelpKind, TyDiagnosticKind, TypedOp, UnaryOutput,
};

macro_rules! current_bodies {
    ($self:ident) => {
        &$self.bodies_map[&$self.current_file.unwrap()]
    };
}

macro_rules! current_module {
    ($self:ident) => {
        $self.modules.get_mut(&$self.current_file.unwrap()).unwrap()
    };
}

macro_rules! current_local_usages {
    ($self:ident) => {
        $self
            .local_usages
            .entry($self.current_file.unwrap())
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
            _ => None,
        }
    }
}

impl InferenceCtx<'_> {
    pub(crate) fn finish_body(
        &mut self,
        body: Idx<Expr>,
        param_tys: Option<Vec<Intern<Ty>>>,
        expected_ty: Option<Intern<Ty>>,
        global: bool,
    ) -> Intern<Ty> {
        let old_param_tys = match param_tys {
            Some(new_param_tys) => self.param_tys.replace(new_param_tys),
            None => self.param_tys.take(),
        };
        let old_local_usages = self
            .local_usages
            .insert(self.current_file.unwrap(), Default::default());

        self.infer_expr(body);

        let local_usages = current_local_usages!(self).clone();
        for (def, usages) in local_usages.iter() {
            current_local_usages!(self).get_mut(def).unwrap().clear();

            self.reinfer_usages(usages.clone());
        }

        let mut actual_ty = self.reinfer_expr(body);

        if let Some(old_local_usages) = old_local_usages {
            self.local_usages
                .insert(self.current_file.unwrap(), old_local_usages);
        }
        self.param_tys = old_param_tys;

        let i32 = Ty::IInt(32).into();
        if let Some(expected_ty) = expected_ty {
            self.expect_match(actual_ty, expected_ty, body);
            self.replace_weak_tys(body, expected_ty);

            actual_ty = expected_ty;
        } else if global && self.replace_weak_tys(body, i32) {
            actual_ty = i32;
        }

        if global && !self.is_const(body) {
            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::GlobalNotConst,
                module: self.current_file.unwrap(),
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
                    if user_local_body.ty.is_none() {
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
        let expr_body = &current_bodies!(self)[expr];
        if matches!(expr_body, Expr::Missing) {
            return false;
        }

        let found_ty = &current_module!(self).expr_tys[expr];
        if !found_ty.is_weak_type_replaceable_by(&new_ty) {
            return false;
        }

        let expr_body = expr_body.clone();

        current_module!(self).expr_tys.insert(expr, new_ty);

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
                            module: self.current_file.unwrap(),
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
                if let Some(scope_id) = current_bodies!(self).block_to_scope_id(expr) {
                    for usage in current_bodies!(self).scope_id_usages(scope_id) {
                        if let hir::Stmt::Break {
                            value: Some(value), ..
                        } = current_bodies!(self)[*usage]
                        {
                            self.replace_weak_tys(value, new_ty);
                        }
                    }
                }
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
            Expr::While {
                condition: None, ..
            } => {
                if let Some(scope_id) = current_bodies!(self).block_to_scope_id(expr) {
                    for usage in current_bodies!(self).scope_id_usages(scope_id) {
                        if let hir::Stmt::Break {
                            value: Some(value), ..
                        } = current_bodies!(self)[*usage]
                        {
                            self.replace_weak_tys(value, new_ty);
                        }
                    }
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
                    Ty::Pointer {
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
            | Expr::Lambda(_)
            | Expr::Import(_)
            | Expr::PrimitiveTy { .. }
            | Expr::StructDecl { .. }
            | Expr::Distinct { .. }
            | Expr::Comptime(_)
            | Expr::StringLiteral(_)
            | Expr::IntLiteral(_)
            | Expr::FloatLiteral(_)
            | Expr::BoolLiteral(_) => true,
            Expr::Array { items, .. } => match items {
                Some(items) => items.iter().all(|item| self.is_const(*item)),
                None => true,
            },
            _ => matches!(
                *(self.modules[&self.current_file.unwrap()][expr]),
                Ty::Type | Ty::File(_)
            ),
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
                deref || self.modules[&self.current_file.unwrap()][*array].is_pointer(),
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
                let local_def = &current_bodies!(self)[*local_def];

                if local_def.mutable {
                    ExprMutability::Mutable
                } else {
                    ExprMutability::ImmutableBinding(local_def.range)
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
            Expr::LocalGlobal(name) => {
                let fqn = hir::Fqn {
                    file: self.current_file.unwrap(),
                    name: name.name,
                };

                ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
            }
            Expr::Path { previous, field } => {
                let previous_ty = self.modules[&self.current_file.unwrap()][*previous];
                match previous_ty.as_ref() {
                    Ty::File(file) => {
                        let fqn = hir::Fqn {
                            file: *file,
                            name: field.name,
                        };

                        if *file == self.current_file.unwrap() {
                            ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
                        } else {
                            ExprMutability::ImmutableGlobal(field.range)
                        }
                    }
                    _ if deref => {
                        let path_ty = &self.modules[&self.current_file.unwrap()][expr];

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
                let ty = self.modules[&self.current_file.unwrap()][expr];

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

    fn infer_stmt(&mut self, stmt: Idx<hir::Stmt>) {
        match &current_bodies!(self)[stmt] {
            hir::Stmt::Expr(expr) => {
                self.infer_expr(*expr);

                self.find_usages(&[*expr], LocalUsage::Expr(*expr));
            }
            hir::Stmt::LocalDef(local_def) => {
                let def_body = &current_bodies!(self)[*local_def];
                let value_ty = self.infer_expr(def_body.value);

                if let Some(ty_annotation) = def_body.ty {
                    let ty_annotation =
                        self.parse_expr_to_ty(ty_annotation, &mut FxHashSet::default());

                    // the definition has an annotation, so the value should match
                    if self.expect_match(value_ty, ty_annotation, def_body.value)
                        && self.replace_weak_tys(def_body.value, ty_annotation)
                    {
                        current_module!(self)
                            .expr_tys
                            .insert(def_body.value, ty_annotation);
                    }
                    current_module!(self)
                        .local_tys
                        .insert(*local_def, ty_annotation);
                } else {
                    // the definition does not have an annotation,
                    // so use the type of it's value
                    current_module!(self).local_tys.insert(*local_def, value_ty);
                }

                self.find_usages(&[def_body.value], LocalUsage::Def(*local_def));
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
                        module: self.current_file.unwrap(),
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
            }
            hir::Stmt::Break { label, value, .. } => {
                let Some(label) = label else { return };
                let referenced_expr = current_bodies!(self)[*label];

                let value_ty = value.map_or(Ty::Void.into(), |value| self.infer_expr(value));

                let must_be_void = matches!(
                    current_bodies!(self)[referenced_expr],
                    Expr::Block {
                        tail_expr: None,
                        ..
                    } | Expr::While {
                        condition: Some(_),
                        ..
                    }
                );

                match self.modules[&self.current_file.unwrap()]
                    .expr_tys
                    .get(referenced_expr)
                {
                    Some(expected_ty) => {
                        self.expect_block_match(
                            value.unwrap(),
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
                                module: self.current_file.unwrap(),
                                range: current_bodies!(self).range_for_expr(value.unwrap()),
                                help: None,
                            });
                        } else {
                            current_module!(self)
                                .expr_tys
                                .insert(referenced_expr, value_ty);
                        }
                    }
                }
            }
            hir::Stmt::Continue { .. } => {
                // there's not really anything to check here
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
            Expr::CharLiteral(_) => {}
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
                if let Some(items) = items {
                    for item in items {
                        self.get_referenced_locals(*item, local_defs);
                    }
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
            Expr::LocalGlobal(_) => {}
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
            Expr::Distinct { .. } => {}
            Expr::StructDecl { .. } => {}
            Expr::Import(_) => {}
        }
    }

    fn reinfer_stmt(&mut self, stmt: Idx<hir::Stmt>) -> Option<Intern<Ty>> {
        match current_bodies!(self)[stmt] {
            hir::Stmt::Break {
                value: Some(value), ..
            } => Some(self.reinfer_expr(value)),
            hir::Stmt::Break { value: None, .. } => Some(Ty::Void.into()),
            _ => None,
        }
    }

    fn reinfer_expr(&mut self, expr: Idx<hir::Expr>) -> Intern<Ty> {
        let previous_ty = current_module!(self)[expr];
        if *previous_ty == Ty::Unknown {
            return previous_ty;
        }

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
                    Ty::Pointer {
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
                        .unwrap_or_else(|| Ty::Unknown.into())
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
            Expr::Array {
                items: Some(items), ..
            } => {
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
                        .unwrap_or_else(|| Ty::Unknown.into())
                } else {
                    return current_module!(self)[expr];
                }
            }
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => {
                let new_tail = self.reinfer_expr(*tail_expr);
                let new_ty = if let Some(label_id) = current_bodies!(self).block_to_scope_id(expr) {
                    let usages = current_bodies!(self).scope_id_usages(label_id);

                    let first_usage_ty = usages.first().and_then(|first| self.reinfer_stmt(*first));
                    for usage in usages.iter().skip(1) {
                        self.reinfer_stmt(*usage);
                    }

                    first_usage_ty.unwrap_or(new_tail)
                } else {
                    new_tail
                };

                let old_ty = current_module!(self)[expr];
                if old_ty != new_ty {
                    new_tail
                } else {
                    return old_ty;
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

                let new_body = self.reinfer_expr(*body);

                let max = if let Some(else_branch) = else_branch {
                    let new_else = self.reinfer_expr(*else_branch);

                    new_body.max(&new_else).unwrap_or(Ty::Unknown).into()
                } else {
                    new_body
                };

                let old_if = current_module!(self)[expr];
                if old_if != max {
                    max
                } else {
                    return old_if;
                }
            }
            Expr::While { condition, body } => {
                if let Some(condition) = condition {
                    self.reinfer_expr(*condition);
                }

                let new_body = self.reinfer_expr(*body);
                let new_ty = if condition.is_some() {
                    Ty::Void.into()
                } else if let Some(label_id) = current_bodies!(self).block_to_scope_id(expr) {
                    let usages = current_bodies!(self).scope_id_usages(label_id);

                    let first_usage_ty = usages.first().and_then(|first| self.reinfer_stmt(*first));
                    for usage in usages.iter().skip(1) {
                        self.reinfer_stmt(*usage);
                    }

                    first_usage_ty.unwrap_or(new_body)
                } else {
                    new_body
                };

                let old_ty = current_module!(self)[expr];
                if old_ty != new_ty {
                    new_body
                } else {
                    return old_ty;
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

    pub(crate) fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> Intern<Ty> {
        if let Some(ty) = current_module!(self).expr_tys.get(expr) {
            return *ty;
        }

        let ty = match &current_bodies!(self)[expr] {
            hir::Expr::Missing => Ty::Unknown.into(),
            hir::Expr::IntLiteral(_) => Ty::UInt(0).into(),
            hir::Expr::FloatLiteral(_) => Ty::Float(0).into(),
            hir::Expr::BoolLiteral(_) => Ty::Bool.into(),
            hir::Expr::StringLiteral(_) => Ty::String.into(),
            hir::Expr::CharLiteral(_) => Ty::Char.into(),
            hir::Expr::Array { size, items, ty } => {
                let sub_ty = self.parse_expr_to_ty(*ty, &mut FxHashSet::default());

                if let Some(items) = items {
                    for item in items {
                        let item_ty = self.infer_expr(*item);
                        self.expect_match(item_ty, sub_ty, *item);
                    }

                    Ty::Array {
                        size: size.unwrap_or(items.len() as u64),
                        sub_ty,
                    }
                    .into()
                } else {
                    Ty::Type.into()
                }
            }
            hir::Expr::Index { array, index } => {
                let source_ty = self.infer_expr(*array);
                // because it's annoying to do `foo^[0]`, this code lets you do `foo[0]`
                let mut deref_source_ty = source_ty;
                while let Some((_, sub_ty)) = deref_source_ty.as_pointer() {
                    deref_source_ty = sub_ty;
                }

                let index_ty = self.infer_expr(*index);

                if *deref_source_ty == Ty::Unknown {
                    Ty::Unknown.into()
                } else if let Some((actual_size, array_sub_ty)) = deref_source_ty.as_array() {
                    if let hir::Expr::IntLiteral(index) = current_bodies!(self)[*index] {
                        if index >= actual_size {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::IndexOutOfBounds {
                                    index,
                                    actual_size,
                                    array_ty: source_ty,
                                },
                                module: self.current_file.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });
                        }
                    }

                    if self.expect_match(index_ty, Ty::UInt(u32::MAX).into(), *index) {
                        self.replace_weak_tys(*index, Ty::UInt(u32::MAX).into());
                    }

                    array_sub_ty
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IndexNonArray { found: source_ty },
                        module: self.current_file.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    Ty::Unknown.into()
                }
            }
            hir::Expr::Cast { expr: sub_expr, ty } => {
                let expr_ty = self.infer_expr(*sub_expr);

                if *expr_ty == Ty::Unknown {
                    Ty::Unknown.into()
                } else {
                    let cast_ty = self.parse_expr_to_ty(*ty, &mut FxHashSet::default());

                    if cast_ty.is_unknown() {
                        Ty::Unknown.into()
                    } else {
                        if !expr_ty.primitive_castable(&cast_ty) {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Uncastable {
                                    from: expr_ty,
                                    to: cast_ty,
                                },
                                module: self.current_file.unwrap(),
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

                if *inner_ty == Ty::Type {
                    inner_ty
                } else {
                    if *mutable {
                        let help = self.get_mutability(*inner, false, false).into_diagnostic();

                        if help.is_some() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::MutableRefToImmutableData,
                                module: self.current_file.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
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
            hir::Expr::Deref { pointer } => {
                let deref_ty = self.infer_expr(*pointer);

                match *deref_ty {
                    Ty::Pointer { sub_ty, .. } if *sub_ty == Ty::Any => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::DerefAny,
                            module: self.current_file.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });

                        Ty::Unknown.into()
                    }
                    Ty::Pointer { sub_ty, .. } => sub_ty,
                    _ => {
                        if !deref_ty.is_unknown() {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::DerefNonPointer { found: deref_ty },
                                module: self.current_file.unwrap(),
                                range: current_bodies!(self).range_for_expr(expr),
                                help: None,
                            });
                        }

                        Ty::Unknown.into()
                    }
                }
            }
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs_ty = self.infer_expr(*lhs);
                let rhs_ty = self.infer_expr(*rhs);

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
                            module: self.current_file.unwrap(),
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
                        module: self.current_file.unwrap(),
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
                        module: self.current_file.unwrap(),
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
                    Some(tail) => {
                        let tail_ty = self.infer_expr(*tail);

                        // there might've been a break within this block
                        // that break would've set the type of this block
                        let previous_ty = self.modules[&self.current_file.unwrap()]
                            .expr_tys
                            .get(expr)
                            .copied();

                        match previous_ty {
                            Some(previous_ty) => {
                                if let Some(max) =
                                    self.expect_block_match(*tail, tail_ty, expr, previous_ty)
                                {
                                    // if there was a previous_ty, then there must've been a break,
                                    // and so this block must have a scope id
                                    let id = current_bodies!(self).block_to_scope_id(expr).unwrap();
                                    for usage in current_bodies!(self).scope_id_usages(id) {
                                        if let hir::Stmt::Break {
                                            value: Some(value), ..
                                        } = current_bodies!(self)[*usage]
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
                    None => Ty::Void.into(),
                }
            }
            hir::Expr::If {
                condition,
                body,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(*condition);
                self.expect_match(cond_ty, Ty::Bool.into(), *condition);

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
                            module: self.current_file.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });

                        Ty::Unknown.into()
                    }
                } else {
                    if *body_ty != Ty::Void && !body_ty.is_unknown() {
                        // only get the range if the body isn't unknown
                        // otherwise we might be getting the range of something that doesn't exist
                        let help_range = match &current_bodies!(self)[*body] {
                            Expr::Block {
                                tail_expr: Some(tail_expr),
                                ..
                            } => current_bodies!(self).range_for_expr(*tail_expr),
                            _ => current_bodies!(self).range_for_expr(*body),
                        };

                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MissingElse { expected: body_ty },
                            module: self.current_file.unwrap(),
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
                    self.expect_match(cond_ty, Ty::Bool.into(), *condition);
                }
                let body_ty = self.infer_expr(*body);
                self.expect_match(body_ty, Ty::Void.into(), *body);

                if let Some(previous_ty) = current_module!(self).expr_tys.get(expr) {
                    *previous_ty
                } else {
                    Ty::Void.into()
                }
            }
            hir::Expr::Local(local) => current_module!(self).local_tys[*local],
            hir::Expr::Param { idx, .. } => self.param_tys.as_ref().unwrap()[*idx as usize],
            hir::Expr::LocalGlobal(name) => {
                let fqn = hir::Fqn {
                    file: self.current_file.unwrap(),
                    name: name.name,
                };

                let sig = self.get_signature(fqn);

                if *sig.0 == Ty::NotYetResolved {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::NotYetResolved { fqn },
                        module: self.current_file.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    Ty::Unknown.into()
                } else {
                    sig.0
                }
            }
            hir::Expr::Path { previous, field } => {
                let previous_ty = self.infer_expr(*previous);
                match previous_ty.as_ref() {
                    Ty::File(file) => {
                        let fqn = hir::Fqn {
                            file: *file,
                            name: field.name,
                        };

                        let definition = self.world_index.get_definition(fqn);

                        match definition {
                            Ok(_) => {
                                let sig = self.get_signature(fqn);

                                if *sig.0 == Ty::NotYetResolved {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::NotYetResolved { fqn },
                                        module: self.current_file.unwrap(),
                                        range: current_bodies!(self).range_for_expr(expr),
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                } else {
                                    sig.0
                                }
                            }
                            Err(hir::GetDefinitionError::UnknownFile) => {
                                unreachable!("a module wasn't added: {:?}", file)
                            }
                            Err(hir::GetDefinitionError::UnknownDefinition) => {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::UnknownFqn { fqn },
                                    module: self.current_file.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
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
                                        module: self.current_file.unwrap(),
                                        range: current_bodies!(self).range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                Ty::Unknown.into()
                            }
                        } else {
                            if !previous_ty.is_unknown() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::NonExistentField {
                                        field: field.name.0,
                                        found_ty: previous_ty,
                                    },
                                    module: self.current_file.unwrap(),
                                    range: current_bodies!(self).range_for_expr(expr),
                                    help: None,
                                });
                            }

                            Ty::Unknown.into()
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
                            module: self.current_file.unwrap(),
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

                    if *callee_ty != Ty::Unknown {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::CalledNonFunction { found: callee_ty },
                            module: self.current_file.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        });
                    }

                    Ty::Unknown.into()
                }
            }
            hir::Expr::Lambda(lambda) => self.infer_lambda(*lambda, None),
            hir::Expr::Comptime(comptime) => {
                let hir::Comptime { body } = current_bodies!(self)[*comptime];

                let ty = self.infer_expr(body);

                if ty.is_pointer() || ty.is_function() {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ComptimePointer,
                        module: self.current_file.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    Ty::Unknown.into()
                } else if *ty == Ty::Type {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ComptimeType,
                        module: self.current_file.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                        help: None,
                    });

                    Ty::Unknown.into()
                } else {
                    ty
                }
            }
            hir::Expr::StructLiteral {
                ty: ty_expr,
                fields: field_values,
            } => {
                let expected_ty = self.parse_expr_to_ty(*ty_expr, &mut FxHashSet::default());

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
                            .insert(expr, Ty::Unknown.into());

                        return Ty::Unknown.into();
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
                            module: self.current_file.unwrap(),
                            range: *found_field_range,
                            help: None,
                        })
                    }
                }

                for expected_field_name in expected_tys
                    .iter()
                    .filter(|(_, ty)| !ty.is_unknown())
                    .map(|(name, _)| name)
                {
                    if found_field_tys.get(expected_field_name).is_none() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::StructLiteralMissingField {
                                field: expected_field_name.0,
                                expected_ty,
                            },
                            module: self.current_file.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                            help: None,
                        })
                    }
                }

                expected_ty
            }
            hir::Expr::PrimitiveTy(_) => Ty::Type.into(),
            hir::Expr::Distinct { ty, .. } => {
                // resolving the type might reveal diagnostics such as recursive types
                self.parse_expr_to_ty(*ty, &mut FxHashSet::default());
                Ty::Type.into()
            }
            hir::Expr::StructDecl { fields, .. } => {
                for (_, ty) in fields {
                    self.parse_expr_to_ty(*ty, &mut FxHashSet::default());
                }
                Ty::Type.into()
            }
            Expr::Import(file_name) => Ty::File(*file_name).into(),
        };

        current_module!(self).expr_tys.insert(expr, ty);

        ty
    }

    /// Only call for blocks which had their type previously set by a `break`
    ///
    /// returns the max of the found expression and the current type of the block
    fn expect_block_match(
        &mut self,
        found_expr: Idx<hir::Expr>,
        found_ty: Intern<Ty>,
        block_expr: Idx<hir::Expr>,
        block_ty: Intern<Ty>,
    ) -> Option<Intern<Ty>> {
        if found_ty.is_unknown() || block_ty.is_unknown() {
            return None;
        }

        if let Some(max) = block_ty.max(&found_ty) {
            let max = max.into();
            current_module!(self).expr_tys[block_expr] = max;
            self.replace_weak_tys(found_expr, max);

            Some(max)
        } else {
            // there must be a usage since the block has a type
            let id = current_bodies!(self).block_to_scope_id(block_expr).unwrap();
            let first_usage = current_bodies!(self)
                .scope_id_usages(id)
                .iter()
                .next()
                .unwrap();

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch {
                    expected: block_ty,
                    found: found_ty,
                },
                module: self.current_file.unwrap(),
                range: current_bodies!(self).range_for_expr(found_expr),
                help: Some(TyDiagnosticHelp {
                    kind: TyDiagnosticHelpKind::BreakHere { break_ty: block_ty },
                    range: current_bodies!(self).range_for_stmt(*first_usage),
                }),
            });

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
            (&current_bodies!(self)[expr], expected.as_ref())
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
                        module: self.current_file.unwrap(),
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
            let help = match current_bodies!(self)[expr] {
                hir::Expr::Block {
                    tail_expr: Some(tail_expr),
                    ..
                } => Some(TyDiagnosticHelp {
                    kind: TyDiagnosticHelpKind::TailExprReturnsHere,
                    range: current_bodies!(self).range_for_expr(tail_expr),
                }),
                _ => None,
            };

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch { expected, found },
                module: self.current_file.unwrap(),
                range: current_bodies!(self).range_for_expr(expr),
                help,
            });

            false
        } else {
            true
        }
    }
}

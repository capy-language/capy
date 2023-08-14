use hir::{Expr, TyWithRange};
use la_arena::{Arena, Idx};

use crate::{cast, InferenceCtx, ResolvedTy, TyDiagnostic, TyDiagnosticKind};

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

        let actual_type: ResolvedTy = self.infer_expr(body);

        self.param_tys = old_param_tys;

        actual_type
    }

    fn is_weak_type_replacable(
        resolved_arena: &Arena<ResolvedTy>,
        found: ResolvedTy,
        expected: ResolvedTy,
    ) -> bool {
        // println!("  is_weak_type_replacable({:?}, {:?})", found, expected);
        match (found, expected) {
            (
                ResolvedTy::IInt(0) | ResolvedTy::UInt(0),
                ResolvedTy::IInt(_) | ResolvedTy::UInt(_),
            ) => true,
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
                    && Self::is_weak_type_replacable(
                        resolved_arena,
                        resolved_arena[found_sub_ty],
                        resolved_arena[expected_sub_ty],
                    )
            }
            (
                ResolvedTy::Pointer {
                    sub_ty: found_sub_ty,
                },
                ResolvedTy::Pointer {
                    sub_ty: expected_sub_ty,
                },
            ) => Self::is_weak_type_replacable(
                resolved_arena,
                resolved_arena[found_sub_ty],
                resolved_arena[expected_sub_ty],
            ),
            (
                ResolvedTy::Distinct { uid: found_uid, .. },
                ResolvedTy::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            (found, ResolvedTy::Distinct { ty, .. }) => {
                Self::is_weak_type_replacable(resolved_arena, found, resolved_arena[ty])
            }
            _ => false,
        }
    }

    fn get_ptr_sub_ty(resolved_arena: &Arena<ResolvedTy>, ptr: ResolvedTy) -> ResolvedTy {
        match ptr {
            ResolvedTy::Pointer { sub_ty } => resolved_arena[sub_ty],
            ResolvedTy::Distinct { ty, .. } => {
                Self::get_ptr_sub_ty(resolved_arena, resolved_arena[ty])
            }
            other => panic!("did not expect to find {:?}", other),
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
        // println!(
        //     "replace_weak_tys {:?} {:?}",
        //     current_module!(self).expr_tys[expr],
        //     new_ty
        // );
        if !Self::is_weak_type_replacable(
            self.resolved_arena,
            current_module!(self).expr_tys[expr],
            new_ty,
        ) {
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
                let new_ty = self.resolved_arena.alloc(new_ty);
                self.replace_weak_tys(pointer, ResolvedTy::Pointer { sub_ty: new_ty });
            }
            Expr::Ref { expr } => {
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
                if self.replace_weak_tys(current_bodies!(self)[local_def].value, new_ty) {
                    current_module!(self).local_tys.insert(local_def, new_ty);
                }
            }
            _ => {}
        }

        true
    }

    fn infer_stmt(&mut self, stmt: Idx<hir::Stmt>) -> Option<ResolvedTy> {
        match &current_bodies!(self)[stmt] {
            hir::Stmt::Expr(expr) => {
                self.infer_expr(*expr);
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
                None
            }
            hir::Stmt::LocalSet(local_set) => {
                let set_body = &current_bodies!(self)[*local_set];
                let set_ty = self.infer_expr(set_body.value);

                if let Some(local_def) = set_body.local_def {
                    let def_ty = *current_module!(self).local_tys.get(local_def).unwrap();

                    self.expect_match(set_ty, def_ty, set_body.value);

                    if matches!(
                        (&def_ty, &set_ty),
                        (
                            ResolvedTy::IInt(_) | ResolvedTy::UInt(_),
                            ResolvedTy::IInt(0) | ResolvedTy::UInt(0)
                        )
                    ) {
                        self.replace_weak_tys(set_body.value, def_ty);
                    }
                }

                None
            }
        }
    }

    fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
        let ty = match &current_bodies!(self)[expr] {
            hir::Expr::Missing => ResolvedTy::Unknown,
            hir::Expr::IntLiteral(_) => ResolvedTy::UInt(0),
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
                    source_ty.has_array_semantics(self.resolved_arena)
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
                            });
                        }
                    }

                    let index_ty = self.infer_expr(*index);

                    self.expect_match(index_ty, ResolvedTy::UInt(u32::MAX), *index);

                    array_sub_ty
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IndexMismatch { found: source_ty },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
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
                                });
                            }

                            // replacing the existing type with the casted type
                            self.replace_weak_tys(*sub_expr, cast_ty);

                            cast_ty
                        }
                    }
                }
            }
            hir::Expr::Ref { expr: sub_expr } => {
                let sub_ty = self.infer_expr(*sub_expr);

                if matches!(sub_ty, ResolvedTy::Type) {
                    ResolvedTy::Type
                } else {
                    ResolvedTy::Pointer {
                        sub_ty: self.resolved_arena.alloc(sub_ty),
                    }
                }
            }
            hir::Expr::Deref { pointer } => {
                let deref_ty = self.infer_expr(*pointer);

                match deref_ty {
                    ResolvedTy::Pointer { sub_ty } => self.resolved_arena[sub_ty],
                    _ => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::DerefMismatch { found: deref_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                        });

                        ResolvedTy::Unknown
                    }
                }
            }
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs_ty = self.infer_expr(*lhs);
                let rhs_ty = self.infer_expr(*rhs);

                let (can_perform, default_ty): (&[ResolvedTy], _) = match op {
                    hir::BinaryOp::Add
                    | hir::BinaryOp::Sub
                    | hir::BinaryOp::Mul
                    | hir::BinaryOp::Div => (&[ResolvedTy::IInt(0)], ResolvedTy::IInt(0)),
                    hir::BinaryOp::Lt
                    | hir::BinaryOp::Gt
                    | hir::BinaryOp::Le
                    | hir::BinaryOp::Ge
                    | hir::BinaryOp::Eq
                    | hir::BinaryOp::Ne => {
                        (&[ResolvedTy::IInt(0), ResolvedTy::Type], ResolvedTy::Bool)
                    }
                    hir::BinaryOp::And | hir::BinaryOp::Or => {
                        (&[ResolvedTy::Bool], ResolvedTy::Bool)
                    }
                };

                if let Some(max_ty) = cast::max_cast(self.resolved_arena, lhs_ty, rhs_ty) {
                    if lhs_ty != ResolvedTy::Unknown
                        && rhs_ty != ResolvedTy::Unknown
                        && !can_perform.iter().any(|expected_ty| {
                            cast::has_semantics_of(self.resolved_arena, max_ty, *expected_ty)
                        })
                    {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::OpMismatch {
                                op: *op,
                                first: lhs_ty,
                                second: rhs_ty,
                            },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
                        });
                    }

                    self.replace_weak_tys(*lhs, max_ty);
                    self.replace_weak_tys(*rhs, max_ty);

                    match op {
                        hir::BinaryOp::Add
                        | hir::BinaryOp::Sub
                        | hir::BinaryOp::Mul
                        | hir::BinaryOp::Div => max_ty,
                        _ => ResolvedTy::Bool,
                    }
                } else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::OpMismatch {
                            op: *op,
                            first: lhs_ty,
                            second: rhs_ty,
                        },
                        module: self.current_module.unwrap(),
                        range: current_bodies!(self).range_for_expr(expr),
                    });
                    default_ty
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr_type = self.infer_expr(*expr);

                match op {
                    hir::UnaryOp::Neg => {
                        self.expect_match(expr_type, ResolvedTy::IInt(0), *expr);
                        match expr_type {
                            ResolvedTy::UInt(bit_width) => ResolvedTy::IInt(bit_width),
                            ResolvedTy::IInt(bit_width) => ResolvedTy::UInt(bit_width),
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
                        });

                        body_ty
                    }
                } else {
                    if !matches!(body_ty, ResolvedTy::Unknown | ResolvedTy::Void) {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MissingElse { expected: body_ty },
                            module: self.current_module.unwrap(),
                            range: current_bodies!(self).range_for_expr(expr),
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

        if found == ResolvedTy::Unknown || expected == ResolvedTy::Unknown {
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
            });

            false
        } else {
            true
        }
    }
}

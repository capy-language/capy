use hir::{Expr, TyWithRange};
use la_arena::{Arena, ArenaMap, Idx};
use rustc_hash::FxHashMap;

use crate::{
    cast, get_fn_signature, get_global_signature, resolve_ty, ResolvedTy, Signature, TyDiagnostic,
    TyDiagnosticKind,
};

pub(crate) struct InferenceCtx<'a> {
    pub(crate) twr_arena: &'a Arena<TyWithRange>,
    pub(crate) resolved_arena: &'a mut Arena<ResolvedTy>,
    pub(crate) expr_tys: &'a mut ArenaMap<Idx<hir::Expr>, ResolvedTy>,
    pub(crate) local_tys: &'a mut ArenaMap<Idx<hir::LocalDef>, ResolvedTy>,
    pub(crate) param_tys: &'a [ResolvedTy],
    pub(crate) bodies: &'a hir::Bodies,
    pub(crate) module: hir::Name,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) diagnostics: &'a mut Vec<TyDiagnostic>,
    pub(crate) signatures: &'a mut FxHashMap<hir::Fqn, Signature>,
}

impl InferenceCtx<'_> {
    pub(crate) fn finish(mut self, body: Idx<Expr>, expected_type: ResolvedTy) {
        let actual_type = self.infer_expr(body);
        self.expect_match(actual_type, expected_type, body);
        self.infer_weak_tys(body, expected_type);
    }

    fn is_weak_type_replacable(
        resolved_arena: &Arena<ResolvedTy>,
        found: ResolvedTy,
        expected: ResolvedTy,
    ) -> bool {
        // println!("is_weak_type_replacable({:?}, {:?})", found, expected);
        let res = match (found, expected) {
            (
                ResolvedTy::IInt(0) | ResolvedTy::UInt(0),
                ResolvedTy::IInt(_) | ResolvedTy::UInt(_),
            ) => true,
            (ResolvedTy::IInt(0) | ResolvedTy::UInt(0), ResolvedTy::Distinct { ty, .. }) => {
                Self::is_weak_type_replacable(resolved_arena, found, resolved_arena[ty])
            }
            (
                ResolvedTy::Distinct { uid: found_uid, .. },
                ResolvedTy::Distinct {
                    uid: expected_uid, ..
                },
            ) => found_uid == expected_uid,
            _ => found == expected,
        };
        // println!("- {}", res);
        res
    }

    /// recursively infers weakly-typed expressions into strong types.
    ///
    /// ```text
    /// x := 42;        // x is of type {uint}, which is an inferable type
    /// y : u16 = x;    // the compiler infers the type of x to u16 instead of throwing an error
    /// ```
    ///
    /// returns true if `expr` had a weak type, returns false if `expr` had a strong type
    fn infer_weak_tys(&mut self, expr: Idx<hir::Expr>, new_ty: ResolvedTy) -> bool {
        println!("should replace {:?} with {:?}?", self.bodies[expr], new_ty);

        if !Self::is_weak_type_replacable(&self.resolved_arena, self.expr_tys[expr], new_ty) {
            println!("nah");
            return false;
        }

        println!("yes");

        self.expr_tys.insert(expr, new_ty.clone());

        match self.bodies[expr] {
            Expr::Block {
                tail_expr: Some(tail_expr),
                ..
            } => {
                self.infer_weak_tys(tail_expr, new_ty);
            }
            Expr::If {
                body, else_branch, ..
            } => {
                self.infer_weak_tys(body, new_ty);
                if let Some(else_branch) = else_branch {
                    self.infer_weak_tys(else_branch, new_ty);
                }
            }
            Expr::Binary { lhs, rhs, .. } => {
                self.infer_weak_tys(lhs, new_ty);
                self.infer_weak_tys(rhs, new_ty);
            }
            Expr::Unary { expr, .. } => {
                self.infer_weak_tys(expr, new_ty);
            }
            Expr::Local(local_def) => {
                if self.infer_weak_tys(self.bodies[local_def].value, new_ty) {
                    self.local_tys.insert(local_def, new_ty.clone());
                }
            }
            _ => {}
        }

        true
    }

    fn infer_stmt(&mut self, stmt: Idx<hir::Stmt>) -> Option<ResolvedTy> {
        match &self.bodies[stmt] {
            hir::Stmt::Expr(expr) => {
                self.infer_expr(*expr);
                None
            }
            hir::Stmt::LocalDef(local_def) => {
                let def_body = &self.bodies[*local_def];
                let value_ty = self.infer_expr(def_body.value);

                let def_ty = resolve_ty(
                    def_body.ty.clone(),
                    self.module,
                    self.world_index,
                    self.twr_arena,
                    self.resolved_arena,
                    self.diagnostics,
                );

                match &def_ty {
                    ResolvedTy::Unknown => {
                        // the definition does not have an annotation, so use the type of it's value
                        self.local_tys.insert(*local_def, value_ty);
                    }
                    def_ty => {
                        // the definition has an annotation, so the value should match
                        if self.expect_match(value_ty, *def_ty, def_body.value)
                            && self.infer_weak_tys(def_body.value, *def_ty)
                        {
                            self.expr_tys.insert(def_body.value, def_ty.clone());
                        }
                        self.local_tys.insert(*local_def, def_ty.clone());
                    }
                }
                None
            }
            hir::Stmt::LocalSet(local_set) => {
                let set_body = &self.bodies[*local_set];
                let set_ty = self.infer_expr(set_body.value);

                if let Some(local_def) = set_body.local_def {
                    let def_ty = self.local_tys.get(local_def).unwrap().clone();

                    self.expect_match(set_ty, def_ty, set_body.value);

                    if matches!(
                        (&def_ty, &set_ty),
                        (
                            ResolvedTy::IInt(_) | ResolvedTy::UInt(_),
                            ResolvedTy::IInt(0) | ResolvedTy::UInt(0)
                        )
                    ) {
                        self.infer_weak_tys(set_body.value, def_ty);
                    }
                }

                None
            }
        }
    }

    fn infer_expr(&mut self, expr: Idx<hir::Expr>) -> ResolvedTy {
        let ty = match &self.bodies[expr] {
            hir::Expr::Missing => ResolvedTy::Unknown,
            hir::Expr::IntLiteral(_) => ResolvedTy::UInt(0),
            hir::Expr::BoolLiteral(_) => ResolvedTy::Bool,
            hir::Expr::StringLiteral(_) => ResolvedTy::String,
            hir::Expr::Array { items, ty } => {
                let sub_ty = resolve_ty(
                    ty.clone(),
                    self.module,
                    self.world_index,
                    self.twr_arena,
                    self.resolved_arena,
                    self.diagnostics,
                );

                for item in items {
                    let item_ty = self.infer_expr(*item);
                    self.expect_match(item_ty, sub_ty, *item);
                }

                ResolvedTy::Array {
                    size: items.len() as u32,
                    sub_ty: self.resolved_arena.alloc(sub_ty),
                }
            }
            hir::Expr::Index { array, index } => {
                let array_ty = self.infer_expr(*array);
                match array_ty {
                    ResolvedTy::Array { sub_ty, .. } => {
                        let index_ty = self.infer_expr(*index);

                        self.expect_match(index_ty, ResolvedTy::UInt(u32::MAX), *index);

                        self.resolved_arena[sub_ty]
                    }
                    _ => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IndexMismatch {
                                found: array_ty.clone(),
                            },
                            range: self.bodies.range_for_expr(expr),
                        });

                        ResolvedTy::Unknown
                    }
                }
            }
            hir::Expr::Cast { expr: sub_expr, ty } => {
                let expr_ty = self.infer_expr(*sub_expr);

                match ty {
                    TyWithRange::Unknown => expr_ty,
                    _ => {
                        let cast_ty = resolve_ty(
                            *ty,
                            self.module,
                            self.world_index,
                            self.twr_arena,
                            self.resolved_arena,
                            self.diagnostics,
                        );

                        if !cast::primitive_castable(expr_ty, cast_ty) {
                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::Uncastable {
                                    from: expr_ty,
                                    to: cast_ty,
                                },
                                range: self.bodies.range_for_expr(expr),
                            });
                        }

                        // replacing the existing type with the casted type
                        self.infer_weak_tys(*sub_expr, cast_ty);

                        cast_ty
                    }
                }
            }
            hir::Expr::Ref { expr: sub_expr } => {
                let sub_ty = self.infer_expr(*sub_expr);

                ResolvedTy::Pointer {
                    sub_ty: self.resolved_arena.alloc(sub_ty),
                }
            }
            hir::Expr::Deref { pointer } => {
                let deref_ty = self.infer_expr(*pointer);

                match deref_ty {
                    ResolvedTy::Pointer { sub_ty } => self.resolved_arena[sub_ty],
                    _ => {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::DerefMismatch {
                                found: deref_ty.clone(),
                            },
                            range: self.bodies.range_for_expr(expr),
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

                if let Some(real_ty) = cast::max_cast(self.resolved_arena, lhs_ty, rhs_ty) {
                    if lhs_ty != ResolvedTy::Unknown
                        && rhs_ty != ResolvedTy::Unknown
                        && !can_perform.into_iter().any(|expected_ty| {
                            cast::has_semantics_of(self.resolved_arena, real_ty, *expected_ty)
                        })
                    {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::OpMismatch {
                                op: *op,
                                first: lhs_ty,
                                second: rhs_ty,
                            },
                            range: self.bodies.range_for_expr(expr),
                        });
                    }
                    match op {
                        hir::BinaryOp::Add
                        | hir::BinaryOp::Sub
                        | hir::BinaryOp::Mul
                        | hir::BinaryOp::Div => real_ty,
                        _ => ResolvedTy::Bool,
                    }
                } else {
                    println!("op mismatch");
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::OpMismatch {
                            op: *op,
                            first: lhs_ty,
                            second: rhs_ty,
                        },
                        range: self.bodies.range_for_expr(expr),
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
                        self.infer_weak_tys(*body, real_ty);
                        self.infer_weak_tys(*else_branch, real_ty);
                        real_ty
                    } else {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::IfMismatch {
                                found: body_ty.clone(),
                                expected: else_ty,
                            },
                            range: self.bodies.range_for_expr(expr),
                        });

                        body_ty
                    }
                } else {
                    if !matches!(body_ty, ResolvedTy::Unknown | ResolvedTy::Void) {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::MissingElse {
                                expected: body_ty.clone(),
                            },
                            range: self.bodies.range_for_expr(expr),
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
            hir::Expr::Local(local) => self.local_tys[*local].clone(),
            hir::Expr::Param { idx } => self.param_tys[*idx as usize].clone(),
            hir::Expr::Call { path, args } => {
                let definition = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => self
                        .world_index
                        .get_definition(hir::Fqn {
                            module: self.module,
                            name,
                        })
                        .unwrap(),
                    hir::PathWithRange::OtherModule { fqn, .. } => {
                        self.world_index.get_definition(fqn).unwrap()
                    }
                };

                let function = match definition {
                    hir::Definition::Function(f) => f,
                    _ => todo!(),
                };

                let fqn = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn {
                        module: self.module,
                        name,
                    },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let function_signature = self
                    .signatures
                    .entry(fqn)
                    .or_insert_with(|| {
                        get_fn_signature(
                            function,
                            self.module,
                            self.world_index,
                            self.twr_arena,
                            self.resolved_arena,
                            self.diagnostics,
                        )
                    })
                    .as_function()
                    .cloned()
                    .unwrap();

                for (idx, arg) in args.iter().enumerate() {
                    let arg_ty = self.infer_expr(*arg);
                    let param_ty = function_signature.param_tys[idx];
                    self.expect_match(arg_ty, param_ty, *arg);

                    self.infer_weak_tys(*arg, param_ty);
                }

                function_signature.return_ty
            }
            hir::Expr::Global(path) => {
                let definition = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => self
                        .world_index
                        .get_definition(hir::Fqn {
                            module: self.module,
                            name,
                        })
                        .unwrap(),
                    hir::PathWithRange::OtherModule { fqn, .. } => {
                        self.world_index.get_definition(fqn).unwrap()
                    }
                };

                let global = match definition {
                    hir::Definition::Global(global) => global,
                    _ => todo!(),
                };

                let fqn = match *path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn {
                        module: self.module,
                        name,
                    },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let global_signature = self
                    .signatures
                    .entry(fqn)
                    .or_insert_with(|| {
                        get_global_signature(
                            global,
                            self.module,
                            self.world_index,
                            self.twr_arena,
                            self.resolved_arena,
                            self.diagnostics,
                        )
                    })
                    .as_global()
                    .unwrap();

                global_signature.ty.clone()
            }
            hir::Expr::Ty { .. } => ResolvedTy::Type,
            hir::Expr::Distinct { .. } => ResolvedTy::Type,
        };

        self.expr_tys.insert(expr, ty.clone());

        ty
    }

    fn expect_match(
        &mut self,
        found: ResolvedTy,
        expected: ResolvedTy,
        expr: Idx<hir::Expr>,
    ) -> bool {
        match (&self.bodies[expr], expected) {
            (
                hir::Expr::IntLiteral(_),
                ResolvedTy::IInt(bit_width) | ResolvedTy::UInt(bit_width),
            ) => {
                if bit_width != u32::MAX {
                    self.expr_tys[expr] = expected.clone();
                }
                return true;
            }
            _ => {}
        };

        if found == ResolvedTy::Unknown || expected == ResolvedTy::Unknown {
            return false;
        }

        if !cast::can_fit(self.resolved_arena, found, expected) {
            let expr = match self.bodies[expr] {
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
                range: self.bodies.range_for_expr(expr),
            });

            false
        } else {
            true
        }
    }
}

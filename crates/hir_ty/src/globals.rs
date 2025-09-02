use std::{collections::HashSet, str::FromStr};

use hir::{
    ArmVariant, Descendant, Expr, FQComptime, FQLambda, LocalDef, MemberLiteral, ScopeId,
    ScopeUsage, Stmt,
};
use indexmap::IndexMap;
use interner::Interner;
use internment::Intern;
use itertools::Itertools;
use la_arena::{ArenaMap, Idx};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use text_size::{TextRange, TextSize};
use topo::TopoSort;

use crate::{
    set_type_name,
    ty::{self, BinaryOutput},
    BuiltinKind, ComptimeResult, EvalComptimeFn, ExpectedTy, FileInference, InferResult,
    Inferrable, InternTyExt, MemberTy, ParamTy, ProjectInference, Ty, TyDiagnostic,
    TyDiagnosticHelp, TyDiagnosticHelpKind, TyDiagnosticKind, TyName, TypedOp, UnaryOutput,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprIsConst {
    /// the value of the expression is known at compile-time
    Const,
    /// the value of the expression is NOT known at compile-time
    Runtime,
    /// the same as `ExprIsConst::Runtime` but doesn't report an error since there's missing information.
    /// the missing information is usually due to incorrect syntax that will have already been
    /// reported by an error elsewhere in the compiler.
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
    CannotMutateExpr(TextRange),
}

impl ExprMutability {
    fn into_diagnostic(self) -> Option<TyDiagnosticHelp> {
        match self {
            ExprMutability::CannotMutateExpr(range) => Some(TyDiagnosticHelp {
                kind: TyDiagnosticHelpKind::CannotMutateExpr,
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

#[derive(Debug, Clone, Copy)]
pub(crate) struct ExprExpected {
    pub(crate) expected_ty: Intern<Ty>,
    pub(crate) annotation_range: TextRange,
    pub(crate) is_return_ty: bool,
    /// this might be true for the `void` return type of `() {}`
    /// but would be false for the `i32` return type of `() -> i32 {}`
    ///
    /// this only works if `is_return_ty` is true
    pub(crate) is_default: bool,
}

pub(crate) struct GlobalInferenceCtx<'a> {
    pub(crate) file: hir::FileName,
    pub(crate) currently_inferring: Inferrable,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) world_bodies: &'a hir::WorldBodies,
    pub(crate) bodies: &'a hir::Bodies,
    pub(crate) interner: &'a Interner,
    // This is used primarily by blocks so that e.g. if a block is not expected to be anything,
    // returned values of `str` and `u64` will cause a type mismatch error to be reported.
    // But if a block is expected to be `str!u64` (via a type annotation or return type),
    // returned values of `str` and `u64` will combine to `str!u64` and there will be no error
    pub(crate) expected_tys: ArenaMap<Idx<hir::Expr>, ExprExpected>,
    // todo: what happens to this when an uninferred global is reached?
    // should this be stored in `InferenceCtx`?
    pub(crate) local_usages: ArenaMap<Idx<hir::LocalDef>, FxHashSet<Idx<hir::Stmt>>>,
    pub(crate) inferred_stmts: &'a mut FxHashSet<(hir::FileName, Idx<hir::Stmt>)>,
    pub(crate) tys: &'a mut ProjectInference,
    pub(crate) param_tys: Vec<ParamTy>,
    pub(crate) all_inferred: &'a FxHashSet<Inferrable>,
    pub(crate) to_infer: &'a mut TopoSort<Inferrable>,
    pub(crate) diagnostics: &'a mut Vec<TyDiagnostic>,
    pub(crate) eval_comptime: &'a mut dyn EvalComptimeFn,
}

impl GlobalInferenceCtx<'_> {
    pub(crate) fn finish_body(
        &mut self,
        body: Idx<Expr>,
        expected_ty: Option<ExprExpected>,
        global: bool,
    ) -> InferResult<Intern<Ty>> {
        if let Some(expected_ty) = expected_ty {
            self.expected_tys.insert(body, expected_ty);
        }

        self.infer_expr(body)?;

        for (_, usages) in self.local_usages.clone() {
            self.reinfer_usages(usages);
        }

        let mut actual_ty = self.reinfer_expr(body);

        let ty_i32 = Ty::IInt(32).into();
        let ty_f64 = Ty::Float(64).into();

        if let Some(expected) = expected_ty {
            self.expect_match(actual_ty, ExpectedTy::Concrete(expected.expected_ty), body);

            actual_ty = expected.expected_ty;
        } else if global && self.replace_weak_tys(body, ty_i32) {
            actual_ty = ty_i32;
        } else if global && self.replace_weak_tys(body, ty_f64) {
            actual_ty = ty_f64;
        }

        // builtin bodies are allowed.
        // I'm not sure if they should be added to `get_const`
        let is_builtin = if let hir::Expr::Directive { name, .. } = self.bodies[body] {
            self.interner.lookup(name.name.0) == "builtin"
        } else {
            false
        };

        if global && self.get_const(body).should_report_not_const() && !is_builtin {
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

                    let dest_ty = self.reinfer_expr(assign_body.dest);
                    let value_ty = self.reinfer_expr(assign_body.value);

                    // this has to be done because in the following example:
                    // ```
                    // main::main :: (() ({
                    //     l0 := (5 #0);
                    //     (l0 #1) += ((1 #2) + (2 #3) #4);
                    //     (l0 #5) -= ((2 #6) + (3 #7) #8);
                    //     (l0 #9) *= ((i64 #11).((3 #10)) #12);
                    //     (l0 #13) /= (4 #14);
                    // } #15) #16);
                    // ```
                    // the statement at #9 will try to `replace_weak_tys` on the value and the dest
                    // with u64, and this `replace_weak_tys` call will eventually call `reinfer_usages`
                    // on the statements at #1, and #5, but while the dest's of these statements (#1
                    // and #5) will get replaced with u64 as expected, their values (#4 and #8)
                    // won't because they never get weak type replaced.
                    //
                    // TODO: this will probably create an infinite loop if the value of the assign
                    // is the variable.
                    match assign_body
                        .quick_assign_op
                        .map(|op| (op, op.get_possible_output_ty(&dest_ty, &value_ty)))
                    {
                        Some((_, Some(output_ty))) => {
                            let max_ty = output_ty.max_ty.into();

                            self.replace_weak_tys(assign_body.dest, max_ty);
                            self.replace_weak_tys(assign_body.value, max_ty);
                        }
                        Some((_, None)) => {}
                        None => {
                            if dest_ty.is_weak_replaceable_by(&value_ty) {
                                self.replace_weak_tys(assign_body.dest, value_ty);
                            } else if value_ty.can_fit_into(&dest_ty) {
                                self.replace_weak_tys(assign_body.value, value_ty);
                            }
                        }
                    }
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
    /// if x > 10 { ... }   // the type of x and 10 here is {uint}
    /// y : u16 = x;        // not only is x's type changed, but the above if condition is changed
    /// ```
    ///
    /// returns true if `expr` had a weak type, returns false if `expr` had a strong type.
    ///
    /// Also when `.[]` gets replaced by a slice, it doesn't actually replace it with the slice,
    /// it will replace it with an array instead. In these cases it will return false.
    fn replace_weak_tys(&mut self, expr: Idx<hir::Expr>, mut new_ty: Intern<Ty>) -> bool {
        let expr_body = &self.bodies[expr];
        if matches!(expr_body, Expr::Missing) {
            return false;
        }

        let found_ty = self.tys[self.file].expr_tys[expr];

        let mut really_replaced = true;

        if !found_ty.is_weak_replaceable_by(&new_ty) {
            return false;
        }

        assert!(
            found_ty.can_fit_into(&new_ty),
            "`is_weak_replaceable_by` is not a subset of `can_fit_into` for `{}` -> `{}`\n(`is_weak_replaceable_by` returned true but `can_fit_into` returned false)",
            found_ty.simple_display(self.interner, true),
            new_ty.simple_display(self.interner, true),
        );

        // if we're trying to replace {uint} with ?u64,
        // what we *should* do is replace {uint} with u64.
        if !found_ty.is_optional()
            && let Ty::Optional { sub_ty } = new_ty.absolute_ty()
        {
            new_ty = *sub_ty;
            really_replaced = false;
        }

        // println!(
        //     "{} #{} : WEAK TYPE {found_ty:?} -> {new_ty:?}",
        //     self.file.debug(self.interner),
        //     expr.into_raw(),
        // );

        if let (Ty::AnonArray { size, sub_ty: _ }, Ty::Slice { sub_ty: new_sub_ty }) =
            (found_ty.as_ref(), new_ty.as_ref())
        {
            new_ty = Ty::ConcreteArray {
                size: *size,
                sub_ty: *new_sub_ty,
            }
            .into();
            really_replaced = false;
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
            Expr::ArrayLiteral { ty: None, items } => match new_ty.as_ref() {
                Ty::ConcreteArray { sub_ty, .. } => {
                    for item in items {
                        self.replace_weak_tys(item, *sub_ty);
                    }
                }
                Ty::Slice { sub_ty } => {
                    let new_ty = Ty::ConcreteArray {
                        size: items.len() as u64,
                        sub_ty: *sub_ty,
                    }
                    .into();

                    self.tys[self.file].expr_tys.insert(expr, new_ty);

                    for item in items {
                        self.replace_weak_tys(item, *sub_ty);
                    }
                }
                _ => unreachable!(),
            },
            Expr::Paren(Some(expr)) => {
                self.replace_weak_tys(expr, new_ty);
            }
            Expr::Block { tail_expr, .. } => {
                if let Some(scope_id) = self.bodies.block_to_scope_id(expr) {
                    for usage in self.bodies.scope_id_usages(scope_id) {
                        match usage {
                            ScopeUsage::Expr(expr) => {
                                assert!(matches!(self.bodies[*expr], hir::Expr::Propagate { .. }));
                                // `.try` resolves to the type of its inner payload, and it doesn't
                                // matter what we resolve to, it won't change the type of the `.try`
                                //
                                // so we don't have to do anything.
                            }
                            ScopeUsage::Stmt(stmt) => {
                                if let hir::Stmt::Break {
                                    value: Some(value), ..
                                } = self.bodies[*stmt]
                                {
                                    self.replace_weak_tys(value, new_ty);
                                }
                            }
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
                        match usage {
                            ScopeUsage::Expr(expr) => {
                                assert!(matches!(self.bodies[*expr], hir::Expr::Propagate { .. }));
                                // we don't have to weak type replace this
                            }
                            ScopeUsage::Stmt(stmt) => {
                                if let hir::Stmt::Break {
                                    value: Some(value), ..
                                } = self.bodies[*stmt]
                                {
                                    self.replace_weak_tys(value, new_ty);
                                }
                            }
                        }
                    }
                }
            }
            Expr::Switch { arms, default, .. } => {
                for arm in arms {
                    self.replace_weak_tys(arm.body, new_ty);
                }
                if let Some(default) = default {
                    self.replace_weak_tys(default.body, new_ty);
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

                // // now get everything that used this variable and make sure the types are correct for those things
                // let usages = self
                //     .local_usages
                //     .get(local_def)
                //     .cloned()
                //     .unwrap_or_default();
                //
                // // now that we have the usages, clear them so no nasty recursion takes place
                // if let Some(usages) = self.local_usages.get_mut(local_def) {
                //     usages.clear();
                // }
                //
                // self.reinfer_usages(usages);

                // self.reinfer_expr(self.bodies[local_def].value);
            }
            Expr::StructLiteral { members, .. } => {
                let member_tys: FxHashMap<hir::Name, Intern<Ty>> = new_ty
                    .as_struct()
                    .unwrap()
                    .iter()
                    .map(|MemberTy { name, ty }| (*name, *ty))
                    .collect();

                for MemberLiteral { name, value } in members.into_iter() {
                    let Some(name) = name else { continue };
                    let new_member_ty = member_tys[&name.name];

                    self.replace_weak_tys(value, new_member_ty);
                }
            }
            _ => {}
        }

        really_replaced
    }

    // `get_const` determines whether or not `const_data` can be called
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
                Expr::Member {
                    previous,
                    name: field,
                } => {
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

                match param_ty.ty.as_pointer() {
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
            Expr::Member {
                previous,
                name: field,
            } => {
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

                let ty = match ty.absolute_ty() {
                    Ty::Optional { sub_ty } => *sub_ty,
                    _ => ty,
                };

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
                    _ => ExprMutability::CannotMutateExpr(self.bodies.range_for_expr(expr)),
                }
            }
            Expr::Paren(Some(expr)) => self.get_mutability(*expr, assignment, deref),
            Expr::Directive { name, args } => {
                match (self.interner.lookup(name.name.0), args.first()) {
                    ("unwrap", Some(arg)) => self.get_mutability(*arg, assignment, deref),
                    _ => ExprMutability::CannotMutateExpr(self.bodies.range_for_expr(expr)),
                }
            }
            _ => ExprMutability::CannotMutateExpr(self.bodies.range_for_expr(expr)),
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
                    Descendant::PreStmt(_) => None,
                    Descendant::PostStmt(_) => unreachable!(),
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
            let block_expr = ctx.bodies.scope_id_to_block(label_id);

            // this is so e.g. if a block lacks an annotation, results of `u64` and `str` should
            // result in errors, but if a block has an annotation of `u64!str`, it becomes legal
            let mut max_ty: Option<Intern<Ty>> =
                ctx.expected_tys.get(block_expr).map(|e| e.expected_ty);

            for usage in usages.iter() {
                let ty = match usage {
                    ScopeUsage::Expr(expr) => match ctx.bodies[*expr] {
                        hir::Expr::Propagate { expr, .. } => ctx.tys[ctx.file][expr]
                            .propagated_ty()
                            .expect("there should be a propagated type"),
                        _ => unreachable!(),
                    },
                    ScopeUsage::Stmt(stmt) => match ctx.bodies[*stmt] {
                        hir::Stmt::Break {
                            value: Some(value), ..
                        } => ctx.tys[ctx.file][value],
                        hir::Stmt::Break { value: None, .. } => Ty::Void.into(),
                        _ => continue,
                    },
                };

                if let Some(old_max) = max_ty {
                    match old_max.max(&ty) {
                        Some(new_max) => max_ty = Some(new_max.into()),
                        None => {
                            // unreachable!(
                            //     "we should've already skipped the expressions that were Ty::Unknown"
                            // );
                            return Ty::Unknown.into();
                        }
                    }
                } else {
                    max_ty = Some(ty);
                }
            }

            max_ty.unwrap_or_else(|| Ty::Void.into())
        }

        #[track_caller]
        fn should_actually_replace(
            ctx: &mut GlobalInferenceCtx,
            expr: Idx<Expr>,
            previous_ty: Intern<Ty>,
            new_ty: Intern<Ty>,
        ) -> bool {
            // loss of distinction might not be accounted for if it happens due to some random
            // annotation somewhere else
            let loss_of_distinct = previous_ty.is_distinct()
                && !new_ty.is_distinct()
                && new_ty.can_fit_into(&previous_ty);

            let array_to_slice = matches!(
                (previous_ty.as_ref(), new_ty.as_ref()),
                (
                    Ty::Slice {
                        sub_ty: previous_sub_ty
                    },
                    Ty::ConcreteArray {
                        sub_ty: new_sub_ty,
                        ..
                    }
                ) if previous_sub_ty.is_weak_replaceable_by(new_sub_ty)
                    || previous_sub_ty == new_sub_ty
            );
            // this might happen in the following case:
            // ```
            // x : u64 = 1;
            // y : i64 = 2;
            //
            // z : i64 = x + y;
            // ```
            // 1. since `u64 + i64` is invalid, the output of `x + y` is {uint} (the
            //    default type of addition).
            // 2. since the value of z is {uint}, it gets weak type replaced by {i64}.
            // 3. reinfer_expr doesn't know about the weak type replacement, so it
            //    attempts to panic here.
            let strong_int_to_weak_int = matches!(
                (previous_ty.as_ref(), new_ty.as_ref()),
                (Ty::UInt(strong_bit_width) | Ty::IInt(strong_bit_width), Ty::UInt(0) | Ty::IInt(0))
                if *strong_bit_width != 0
            );

            // let upgraded_to_error_union = matches!(
            //     (previous_ty.as_ref(), new_ty.as_ref()),
            //     (Ty::ErrorUnion { error_ty, payload_ty }, other)
            //     if error_ty.is_equal_to(other) || payload_ty.is_equal_to(other)
            // );

            let prev_is_expected = ctx
                .expected_tys
                .get(expr)
                .is_some_and(|e| e.expected_ty == previous_ty);

            if !loss_of_distinct && !array_to_slice && !strong_int_to_weak_int && !prev_is_expected
            {
                if (previous_ty != new_ty && !previous_ty.is_weak_replaceable_by(&new_ty))
                    || (new_ty.is_unknown() && !previous_ty.is_unknown())
                {
                    // let's say the previous type of the variable `x` was i32 (due to the type
                    // annotation)
                    //
                    // the "new" type we just got is {uint} (we've re-reviewed all the internal
                    // expressions inside the value of `x` and it results in {uint})
                    //
                    // the previous type doesn't fit into the new type, but that's okay.
                    // the new type *does* fit into the old type.
                    // because of that, we're not gonna panic and we're not gonna replace the type
                    //
                    // we only panic just in case the `reinfer_expr` logic is bad and we get
                    // something completely weird.
                    if new_ty.is_weak_replaceable_by(&previous_ty) {
                        return false;
                    }

                    panic!(
                        "{} #{} : `{}` is not weak replaceable by `{}`",
                        ctx.file.debug(ctx.interner),
                        expr.into_raw(),
                        previous_ty.simple_display(ctx.interner, true),
                        new_ty.simple_display(ctx.interner, true)
                    );
                }

                // println!(
                //     "{} #{} : replacing {:?} with {:?}",
                //     self.file.debug(self.interner),
                //     expr.into_raw(),
                //     previous_ty,
                //     new_ty
                // );
                return true;
            }

            false
        }

        for next in self
            .bodies
            .descendants(
                expr,
                hir::DescentOpts::Infer {
                    include_post_stmts: false,
                },
            )
            .collect_vec()
            .into_iter()
            .rev()
        {
            match next {
                Descendant::Expr(expr) => {
                    let previous_ty = self.tys[self.file]
                        .expr_tys
                        .get(expr)
                        .copied()
                        .unwrap_or_else(|| {
                            panic!(
                                "{} #{} : TYPE DOES NOT EXIST",
                                self.file.debug(self.interner),
                                expr.into_raw()
                            );
                        });

                    if *previous_ty == Ty::Unknown || *previous_ty == Ty::AlwaysJumps {
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
                                } else if usages_ty.is_nil() {
                                    usages_ty
                                        .max(&Ty::Void)
                                        .expect("max should always work")
                                        .into()
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
                            } else if *body_ty == Ty::AlwaysJumps {
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
                        Expr::Member {
                            previous,
                            name: field,
                        } => {
                            // make sure this matches up with the one in infer_expr
                            let super_ty = self.tys[self.file][*previous];
                            match super_ty.as_ref() {
                                Ty::File(_) => continue,
                                Ty::Type => continue,
                                _ => {
                                    // because it's annoying to do `foo^.bar`, this code lets you do `foo.bar`
                                    let mut deref_ty = super_ty;
                                    while let Some((_, sub_ty)) = deref_ty.as_pointer() {
                                        deref_ty = sub_ty;
                                    }
                                    deref_ty = deref_ty.absolute_intern_ty(true);

                                    let field_name = self.interner.lookup(field.name.0);

                                    match (deref_ty.as_ref(), field_name) {
                                        (
                                            Ty::AnonStruct { members }
                                            | Ty::ConcreteStruct { members, .. },
                                            _,
                                        ) => {
                                            if let Some(matching_member) = members
                                                .iter()
                                                .find(|member_ty| member_ty.name == field.name)
                                            {
                                                matching_member.ty
                                            } else {
                                                unreachable!("previous_ty would've been unknown")
                                            }
                                        }
                                        (Ty::Slice { .. }, "len") => continue,
                                        (Ty::Slice { sub_ty }, "ptr") => Ty::Pointer {
                                            mutable: false,
                                            sub_ty: *sub_ty,
                                        }
                                        .into(),
                                        (Ty::RawSlice, "len") => continue,
                                        (Ty::RawSlice, "ptr") => continue,
                                        (Ty::Any, "ty") => continue,
                                        (Ty::Any, "ptr") => continue,
                                        (
                                            Ty::AnonArray { .. } | Ty::ConcreteArray { .. },
                                            "len",
                                        ) => continue,
                                        _ => {
                                            unreachable!(
                                                "previous_ty would've been Ty::Unknown if this was true"
                                            )
                                        }
                                    }
                                }
                            }
                        }
                        _ => {
                            continue;
                        }
                    };

                    if should_actually_replace(self, expr, previous_ty, new_ty) {
                        self.tys[self.file].expr_tys.insert(expr, new_ty);
                    }
                }
                Descendant::PreStmt(stmt) => match &self.bodies[stmt] {
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

                        if should_actually_replace(self, expr, previous_ty, new_ty) {
                            self.tys[self.file].local_tys.insert(*local_def, new_ty);
                        }
                    }
                    Stmt::Assign(_) => {}
                    Stmt::Break { .. } => {}
                    Stmt::Continue { .. } => {}
                    Stmt::Defer { .. } => {}
                },
                Descendant::PostStmt(_) => unreachable!(),
            }
        }

        self.tys[self.file][expr]
    }

    // This function is indent hell but it's worth it to make it stack overflow free
    pub(crate) fn infer_expr(&mut self, expr: Idx<Expr>) -> InferResult<Intern<Ty>> {
        if let (Some(ty), None) = (
            self.tys[self.file].expr_tys.get(expr),
            self.bodies.block_to_scope_id(expr),
        ) {
            return Ok(*ty);
        }

        let descendants = self
            .bodies
            .descendants(
                expr,
                hir::DescentOpts::Infer {
                    include_post_stmts: true,
                },
            )
            .collect_vec();

        // This works without recursion because children will ALWAYS come before parents
        for descendant in descendants.into_iter().rev() {
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
                                self.expect_match(item_ty, ExpectedTy::Concrete(sub_ty), *item);
                            }

                            Ty::ConcreteArray {
                                size: items.len() as u64,
                                sub_ty,
                            }
                            .into()
                        }
                        Expr::ArrayLiteral { ty: None, items } => {
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
                                                                    expected: ExpectedTy::Concrete(
                                                                        previous,
                                                                    ),
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

                            Ty::AnonArray {
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

                            self.expect_match(
                                index_ty,
                                ExpectedTy::Concrete(Ty::UInt(u8::MAX).into()),
                                *index,
                            );

                            if *deref_source_ty == Ty::Unknown {
                                Ty::Unknown.into()
                            } else if *deref_source_ty == Ty::RawSlice {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::IndexRaw,
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

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

                                array_sub_ty
                            } else if let Some(slice_sub_ty) = deref_source_ty.as_slice() {
                                slice_sub_ty
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
                        Expr::Cast { ty, expr: None } => {
                            let cast_ty = self.const_ty(*ty)?;

                            if cast_ty.is_unknown() {
                                Ty::Unknown.into()
                            } else {
                                if !Ty::Void.can_cast_to(&cast_ty) {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::Uncastable {
                                            from: Ty::Void.into(),
                                            to: cast_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });
                                }

                                cast_ty
                            }
                        }
                        Expr::Cast {
                            ty,
                            expr: Some(sub_expr),
                        } => {
                            let cast_from = self.tys[self.file][*sub_expr];

                            if *cast_from == Ty::Unknown {
                                Ty::Unknown.into()
                            } else {
                                let cast_to = self.const_ty(*ty)?;

                                if cast_to.is_unknown() {
                                    Ty::Unknown.into()
                                } else {
                                    if !cast_from.can_cast_to(&cast_to) {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::Uncastable {
                                                from: cast_from,
                                                to: cast_to,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help: None,
                                        });
                                    } else if let Ty::EnumVariant { sub_ty, .. } =
                                        cast_to.absolute_ty_keep_variants()
                                    {
                                        self.replace_weak_tys(*sub_expr, *sub_ty);
                                    } else {
                                        self.replace_weak_tys(*sub_expr, cast_to);
                                    }

                                    cast_to
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
                                Ty::RawPtr { .. } => {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::DerefRaw,
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
                                println!("no max");
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

                            if *op == hir::UnaryOp::BNot && *expr_ty == Ty::Type {
                                // this transforms expressions like `!u64` into error unions
                                self.const_ty(*expr)?;
                                Ty::Type.into()
                            } else if !op.can_perform(&expr_ty) {
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
                                            && *self.tys[self.file][*expr] == Ty::AlwaysJumps =>
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
                                    let previous_ty = self.try_get_previous_ty(expr);

                                    match previous_ty {
                                        Some(previous_ty) => {
                                            // if there were no type errors and the block has a
                                            // scope id (if it has a scope id then that means we
                                            // should replace the weak types of the people who use
                                            // that scope id)
                                            if let Some(max) = self.expect_block_match(
                                                Some(*tail),
                                                tail_ty,
                                                self.bodies.range_for_expr(*tail),
                                                expr,
                                                previous_ty,
                                                true,
                                            ) {
                                                // todo: this is wayyyyy to many indents
                                                for usage in self
                                                    .bodies
                                                    .block_to_scope_id(expr)
                                                    .map(|id| {
                                                        self.bodies.scope_id_usages(id).iter()
                                                    })
                                                    .into_iter()
                                                    .flatten()
                                                {
                                                    match usage {
                                                        ScopeUsage::Expr(expr) => {
                                                            // these don't need to be
                                                            // weak_type_replaced because the max
                                                            // type of the block doesn't affect
                                                            // them.
                                                            assert!(matches!(
                                                                self.bodies[*expr],
                                                                hir::Expr::Propagate { .. }
                                                            ));
                                                        }
                                                        ScopeUsage::Stmt(stmt) => {
                                                            if let hir::Stmt::Break {
                                                                value: Some(value),
                                                                ..
                                                            } = self.bodies[*stmt]
                                                            {
                                                                self.replace_weak_tys(value, max);
                                                            }
                                                        }
                                                    }
                                                }

                                                max
                                            } else {
                                                // println!(
                                                //     "{} #{} : prev_ty={previous_ty:?}, tail_ty={tail_ty:?}",
                                                //     self.file.debug(self.interner),
                                                //     expr.into_raw(),
                                                // );
                                                Ty::Unknown.into()
                                            }
                                        }
                                        None => tail_ty,
                                    }
                                }
                                None if no_eval => {
                                    // todo: maybe this shouldn't use try_get_previous_ty?
                                    // it might be better to check if we have a scope id
                                    let previous_ty = self.try_get_previous_ty(expr);

                                    // if there is no previous type but this block always breaks
                                    // it is 100% certain that the break was for an upper block.
                                    // it is then safe to say this block is "noeval"
                                    // (meaning that it never reaches it's own end)
                                    previous_ty.unwrap_or_else(|| Ty::AlwaysJumps.into())
                                }
                                None => {
                                    // if there were no breaks, Void,
                                    // if there was a break, make sure it's Void
                                    if let Some(previous_ty) = self.try_get_previous_ty(expr) {
                                        if let Some(max) = self.expect_block_match(
                                            Some(expr),
                                            Ty::Void.into(),
                                            self.bodies.range_for_expr(expr),
                                            expr,
                                            previous_ty,
                                            true,
                                        ) {
                                            max
                                        } else {
                                            // println!(
                                            //     "{} #{} : prev_ty={previous_ty:?}",
                                            //     self.file.debug(self.interner),
                                            //     expr.into_raw(),
                                            // );
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
                            self.expect_match(
                                cond_ty,
                                ExpectedTy::Concrete(Ty::Bool.into()),
                                *condition,
                            );

                            let body_ty = self.tys[self.file][*body];

                            if let Some(else_branch) = else_branch {
                                let else_ty = self.tys[self.file][*else_branch];

                                if *else_ty == Ty::Unknown {
                                    else_ty
                                } else if let Some(real_ty) = body_ty.max(&else_ty) {
                                    let real_ty = real_ty.into();
                                    self.replace_weak_tys(*body, real_ty);
                                    self.replace_weak_tys(*else_branch, real_ty);
                                    real_ty
                                } else {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::IfMismatch {
                                            first: body_ty,
                                            second: else_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                }
                            } else {
                                if *body_ty != Ty::AlwaysJumps
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

                                if *body_ty == Ty::AlwaysJumps {
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
                                self.expect_match(
                                    cond_ty,
                                    ExpectedTy::Concrete(Ty::Bool.into()),
                                    *condition,
                                );
                            }
                            let body_ty = self.tys[self.file][*body];
                            self.expect_match(
                                body_ty,
                                ExpectedTy::Concrete(Ty::Void.into()),
                                *body,
                            );

                            if let Some(previous_ty) = self.tys[self.file].expr_tys.get(expr) {
                                *previous_ty
                            } else {
                                Ty::Void.into()
                            }
                        }
                        Expr::Switch {
                            scrutinee,
                            arms,
                            default,
                            ..
                        } => 'switch: {
                            let scrutinee_ty = self.tys[self.file][*scrutinee];

                            if !self.expect_match(scrutinee_ty, ExpectedTy::SumType, *scrutinee) {
                                break 'switch Ty::Unknown.into();
                            }

                            // resolve all arm types beforehand
                            let mut type_resolution_error = false;
                            for arm in arms {
                                match arm.variant {
                                    Some(ArmVariant::FullyQualified(ty)) => {
                                        if !self.expect_match(
                                            self.tys[self.file][ty],
                                            ExpectedTy::Concrete(Ty::Type.into()),
                                            ty,
                                        ) {
                                            type_resolution_error = true;
                                            continue;
                                        }

                                        let ty = self.const_ty(ty)?;

                                        if !scrutinee_ty.has_sum_variant(&ty) {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::NotAVariantOfSumType {
                                                    ty,
                                                    sum_ty: scrutinee_ty,
                                                },
                                                file: self.file,
                                                expr: Some(arm.body),
                                                range: arm.variant_range,
                                                help: None,
                                            });
                                            type_resolution_error = true;
                                        }
                                    }
                                    Some(ArmVariant::Shorthand(name)) => {
                                        // todo: include tests for this
                                        if !self.expect_match(
                                            scrutinee_ty,
                                            ExpectedTy::Enum,
                                            *scrutinee,
                                        ) {
                                            type_resolution_error = true;
                                            continue;
                                        }

                                        let Ty::Enum { ref variants, .. } = *scrutinee_ty else {
                                            unreachable!();
                                        };

                                        if !variants.iter().any(|v| {
                                            let Ty::EnumVariant { variant_name, .. } = **v else {
                                                unreachable!()
                                            };

                                            variant_name == name.name
                                        }) {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::NotAShorthandVariantOfSumType {
                                                    ty: name.name.0,
                                                    sum_ty: scrutinee_ty,
                                                },
                                                file: self.file,
                                                expr: Some(arm.body),
                                                range: arm.variant_range,
                                                help: None,
                                            });
                                            type_resolution_error = true;
                                        }
                                    }
                                    None => {}
                                }
                            }
                            if type_resolution_error {
                                break 'switch Ty::Unknown.into();
                            }

                            struct VariantToCheck {
                                variant_ty: Intern<Ty>,
                                included_in_switch: bool,
                            }

                            impl VariantToCheck {
                                fn matches_arm(
                                    &self,
                                    tys: &FileInference,
                                    variant: ArmVariant,
                                ) -> bool {
                                    match variant {
                                        ArmVariant::FullyQualified(ty) => {
                                            self.variant_ty == tys.get_meta_ty(ty).expect("all the arms should be resolved before calling `matches_arm`")
                                        }
                                        ArmVariant::Shorthand(name) => {
                                            let Ty::EnumVariant { variant_name, .. } = *self.variant_ty else {
                                                unreachable!()
                                            };

                                            variant_name == name.name
                                        }
                                    }
                                }
                            }

                            impl From<Intern<Ty>> for VariantToCheck {
                                fn from(variant_ty: Intern<Ty>) -> Self {
                                    Self {
                                        variant_ty,
                                        included_in_switch: false,
                                    }
                                }
                            }

                            let mut variants: Vec<VariantToCheck> = match *scrutinee_ty {
                                Ty::Optional { sub_ty } => {
                                    vec![sub_ty.into(), Intern::new(Ty::Nil).into()]
                                }
                                Ty::ErrorUnion {
                                    error_ty,
                                    payload_ty,
                                } => vec![error_ty.into(), payload_ty.into()],
                                Ty::Enum { ref variants, .. } => {
                                    variants.iter().map(|v| (*v).into()).collect_vec()
                                }
                                _ => unreachable!(),
                            };

                            let mut first_arm_ty = None;

                            for arm in arms {
                                let Some(variant) = arm.variant else {
                                    // skip the errors
                                    continue;
                                };

                                let Some(arm_variant) = variants
                                    .iter_mut()
                                    .find(|v| v.matches_arm(&self.tys[self.file], variant))
                                else {
                                    unreachable!()
                                };

                                if arm_variant.included_in_switch {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::SwitchAlreadyCoversVariant {
                                            ty: arm_variant.variant_ty,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: arm.variant_range,
                                        help: None, // todo: show the previous arm
                                    });
                                } else {
                                    // if any variants haven't been covered an error will be reported
                                    arm_variant.included_in_switch = true;
                                }

                                let found_arm_ty = self.tys[self.file][arm.body];

                                match first_arm_ty {
                                    None => {
                                        first_arm_ty = Some(found_arm_ty);
                                    }
                                    Some(first_ty) if *first_ty == Ty::Unknown => {}
                                    Some(first_ty) => {
                                        if let Some(real_ty) = first_ty.max(&found_arm_ty) {
                                            let real_ty = real_ty.into();
                                            first_arm_ty = Some(real_ty);
                                        } else {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::SwitchMismatch {
                                                    other: found_arm_ty,
                                                    first: first_ty,
                                                },
                                                file: self.file,
                                                expr: Some(arm.body),
                                                range: self.bodies.range_for_expr(arm.body),
                                                help: None,
                                            });

                                            first_arm_ty = Some(Ty::Unknown.into());
                                        }
                                    }
                                }
                            }

                            if let Some(default) = default {
                                let default_ty = self.tys[self.file][default.body];

                                match first_arm_ty {
                                    None => {
                                        first_arm_ty = Some(default_ty);
                                    }
                                    Some(first_ty) if *first_ty == Ty::Unknown => {}
                                    Some(first_ty) => {
                                        if let Some(real_ty) = first_ty.max(&default_ty) {
                                            let real_ty = real_ty.into();
                                            self.replace_weak_tys(default.body, real_ty);
                                            first_arm_ty = Some(real_ty);
                                        } else {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::SwitchMismatch {
                                                    other: default_ty,
                                                    first: first_ty,
                                                },
                                                file: self.file,
                                                expr: Some(default.body),
                                                range: self.bodies.range_for_expr(default.body),
                                                help: None,
                                            });

                                            first_arm_ty = Some(Ty::Unknown.into());
                                        }
                                    }
                                }
                            } else {
                                for VariantToCheck {
                                    variant_ty,
                                    included_in_switch,
                                } in variants
                                {
                                    if included_in_switch {
                                        continue;
                                    }

                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::SwitchDoesNotCoverVariant {
                                            ty: variant_ty,
                                        },
                                        file: self.file,
                                        range: self.bodies.range_for_expr(expr),
                                        expr: Some(expr),
                                        help: None,
                                    });
                                }
                            }

                            if let Some(first_arm_ty) = first_arm_ty.filter(|t| **t != Ty::Unknown)
                            {
                                for arm in arms {
                                    self.replace_weak_tys(arm.body, first_arm_ty);
                                }
                            }

                            first_arm_ty.unwrap_or_else(|| Ty::Void.into())
                        }
                        Expr::Local(local) => self.tys[self.file].local_tys[*local],
                        Expr::SwitchArgument(switch_local) => 'switch_arg: {
                            if let Some(ty) =
                                self.tys[self.file].switch_local_tys.get(*switch_local)
                            {
                                break 'switch_arg *ty;
                            }

                            let switch_local_body = &self.bodies[*switch_local];
                            let scrutinee_ty = self.tys[self.file][switch_local_body.scrutinee];
                            if switch_local_body.is_default {
                                // default branches just receive the scrutinee as-is
                                break 'switch_arg scrutinee_ty;
                            }

                            let Some(this_variant) = switch_local_body.variant else {
                                break 'switch_arg Ty::Unknown.into();
                            };

                            let variant_ty = match this_variant {
                                ArmVariant::Shorthand(name) => {
                                    let Ty::Enum { variants, .. } = scrutinee_ty.as_ref() else {
                                        // an error will be reported so we don't have to do
                                        // anything here
                                        break 'switch_arg Ty::Unknown.into();
                                    };

                                    variants
                                        .iter()
                                        .find(|v| {
                                            let Ty::EnumVariant { variant_name, .. } = v.as_ref()
                                            else {
                                                unreachable!("all variants should be `Ty::Variant`")
                                            };

                                            *variant_name == name.name
                                        })
                                        .copied()
                                        .unwrap_or_else(|| Ty::Unknown.into())
                                }
                                ArmVariant::FullyQualified(ty) => self.const_ty(ty)?,
                            };

                            self.tys[self.file]
                                .switch_local_tys
                                .insert(*switch_local, variant_ty);

                            variant_ty
                        }
                        Expr::Param { idx, .. } => self.param_tys[*idx as usize].ty,
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
                        Expr::Member {
                            previous,
                            name: field,
                        } => {
                            // make sure this matches up with the one in reinfer_expr
                            let super_ty = self.tys[self.file][*previous];
                            match super_ty.as_ref() {
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
                                Ty::Type => {
                                    // this is included for resolving enum variants
                                    let ty = self.const_ty(expr)?;

                                    // zero-sized types can be used as their own singletons
                                    if ty.is_zero_sized() {
                                        ty
                                    } else {
                                        Ty::Type.into()
                                    }
                                }
                                _ => {
                                    // because it's annoying to do `foo^.bar`, this code lets you do `foo.bar`
                                    let mut deref_ty = super_ty;
                                    while let Some((_, sub_ty)) = deref_ty.as_pointer() {
                                        deref_ty = sub_ty;
                                    }
                                    deref_ty = deref_ty.absolute_intern_ty(true);

                                    let field_name = self.interner.lookup(field.name.0);

                                    match (deref_ty.as_ref(), field_name) {
                                        (
                                            Ty::AnonStruct { members }
                                            | Ty::ConcreteStruct { members, .. },
                                            _,
                                        ) => {
                                            if let Some(matching_member) = members
                                                .iter()
                                                .find(|member_ty| member_ty.name == field.name)
                                            {
                                                matching_member.ty
                                            } else {
                                                if !super_ty.is_unknown() {
                                                    self.diagnostics.push(TyDiagnostic {
                                                        kind: TyDiagnosticKind::NonExistentMember {
                                                            member: field.name.0,
                                                            found_ty: super_ty,
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
                                        (Ty::Slice { .. }, "len") => Ty::UInt(u8::MAX).into(),
                                        (Ty::Slice { sub_ty }, "ptr") => Ty::Pointer {
                                            mutable: false,
                                            sub_ty: *sub_ty,
                                        }
                                        .into(),
                                        (Ty::RawSlice, "len") => Ty::UInt(u8::MAX).into(),
                                        (Ty::RawSlice, "ptr") => {
                                            Ty::RawPtr { mutable: false }.into()
                                        }
                                        (Ty::Any, "ty") => Ty::Type.into(),
                                        (Ty::Any, "ptr") => Ty::RawPtr { mutable: false }.into(),
                                        (
                                            Ty::AnonArray { .. } | Ty::ConcreteArray { .. },
                                            "len",
                                        ) => Ty::UInt(u8::MAX).into(),
                                        _ => {
                                            if !super_ty.is_unknown() {
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::NonExistentMember {
                                                        member: field.name.0,
                                                        found_ty: super_ty,
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
                        }
                        Expr::Call { callee, args } => {
                            let callee_ty = self.tys[self.file][*callee];

                            if let Some((params, return_ty)) = callee_ty.clone().as_function() {
                                let mut params_iter = params.iter();
                                let mut args_iter = args.iter();

                                let mut current_param = params_iter.next();
                                let mut current_arg = args_iter.next();

                                loop {
                                    let Some(arg) = current_arg else {
                                        if let Some(param) = current_param {
                                            // there are more params than args

                                            if param.varargs {
                                                current_param = params_iter.next();
                                                continue; // continue without reporting error
                                            }

                                            let param_ty = param.ty;

                                            let call_range = self.bodies.range_for_expr(expr);
                                            let call_end = call_range
                                                .end()
                                                .checked_sub(TextSize::new(1))
                                                .unwrap_or(call_range.end());

                                            // TODO: add tests for this != Ty::Unknown
                                            if !param.impossible_to_differentiate
                                                && *param_ty != Ty::Unknown
                                            {
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::MissingArg {
                                                        expected: ExpectedTy::Concrete(param_ty),
                                                    },
                                                    file: self.file,
                                                    expr: Some(expr),
                                                    range: TextRange::new(call_end, call_end),
                                                    help: None,
                                                });
                                            }
                                        } else {
                                            break;
                                        }
                                        current_param = params_iter.next();
                                        continue;
                                    };
                                    let arg_ty = self.tys[self.file][*arg];

                                    let Some(param) = current_param else {
                                        // there are more args than params
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::ExtraArg { found: arg_ty },
                                            file: self.file,
                                            expr: Some(*arg),
                                            range: self.bodies.range_for_expr(*arg),
                                            help: None,
                                        });
                                        current_arg = args_iter.next();
                                        continue;
                                    };

                                    if param.varargs {
                                        let actual_sub_ty = param.ty.as_slice().unwrap();

                                        if arg_ty.can_fit_into(&actual_sub_ty) {
                                            self.replace_weak_tys(*arg, actual_sub_ty);

                                            current_arg = args_iter.next();
                                        } else if let Some(next_param) = params_iter.next() {
                                            // go to the next param but don't go to the next arg.
                                            // this basically just reevaluates the current argument
                                            // under the next parameter.
                                            current_param = Some(next_param);
                                        } else {
                                            // `can_fit_into` should return true for unknowns
                                            assert!(!arg_ty.is_unknown());
                                            // this will just return an error
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::Mismatch {
                                                    expected: ExpectedTy::Concrete(actual_sub_ty),
                                                    found: arg_ty,
                                                },
                                                file: self.file,
                                                expr: Some(*arg),
                                                range: self.bodies.range_for_expr(*arg),
                                                help: None,
                                            });
                                            current_arg = args_iter.next();
                                        }
                                    } else {
                                        self.expect_match(
                                            arg_ty,
                                            ExpectedTy::Concrete(param.ty),
                                            *arg,
                                        );

                                        current_param = params_iter.next();
                                        current_arg = args_iter.next();
                                    }
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
                                ..
                            } = &self.bodies[*lambda];

                            let is_type = *body == hir::LambdaBody::Empty && return_ty.is_some();

                            let return_ty = if let Some(return_ty) = return_ty {
                                self.const_ty(*return_ty)?
                            } else {
                                Ty::Void.into()
                            };

                            let mut param_tys = Vec::with_capacity(params.len());

                            for (idx, param) in params.iter().enumerate() {
                                let mut ty = self.const_ty(param.ty)?;

                                let mut impossible_to_differentiate = false;

                                if let Some(last_param) = idx
                                    .checked_sub(1)
                                    .and_then(|idx| params.get(idx))
                                    .filter(|p| p.varargs)
                                {
                                    // we already called `const_ty` on the last param
                                    let last_ty = self.tys[self.file].meta_tys[last_param.ty];

                                    if !ty.can_differentiate_from(&last_ty) {
                                        impossible_to_differentiate = true;
                                        self.diagnostics.push(TyDiagnostic {
                                            kind:
                                                TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                                                    previous_ty: last_ty,
                                                    current_ty: ty,
                                                },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: param.range,
                                            help: None,
                                        });
                                    }
                                }

                                if param.varargs {
                                    ty = Ty::Slice { sub_ty: ty }.into();

                                    if *body == hir::LambdaBody::Extern {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::ExternVarargs,
                                            file: self.file,
                                            expr: Some(expr),
                                            range: param.range,
                                            help: None,
                                        });
                                    }
                                }

                                param_tys.push(ParamTy {
                                    ty,
                                    varargs: param.varargs,
                                    impossible_to_differentiate,
                                });
                            }

                            let ty = Ty::Function {
                                param_tys,
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
                                .filter_map(|MemberLiteral { name, value }| {
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
                            .map(|MemberTy { name, ty }| (name, ty))
                            .collect::<IndexMap<_, _>>();

                            for (
                                found_member_name,
                                (found_member_range, found_member_expr, found_member_ty),
                            ) in found_member_tys.iter()
                            {
                                if let Some(expected_member_ty) =
                                    expected_tys.get(found_member_name)
                                {
                                    self.expect_match(
                                        *found_member_ty,
                                        ExpectedTy::Concrete(*expected_member_ty),
                                        *found_member_expr,
                                    );
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
                        } => Ty::AnonStruct {
                            members: member_values
                                .iter()
                                .copied()
                                .filter_map(|MemberLiteral { name, value }| {
                                    name.map(|name| MemberTy {
                                        name: name.name,
                                        ty: self.tys[self.file][value],
                                    })
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
                        Expr::EnumDecl { .. } => {
                            self.const_ty(expr)?;
                            Ty::Type.into()
                        }
                        Expr::Nil => Ty::Nil.into(),
                        Expr::OptionalDecl { .. } => {
                            self.const_ty(expr)?;
                            Ty::Type.into()
                        }
                        Expr::ErrorUnionDecl { .. } => {
                            self.const_ty(expr)?;
                            Ty::Type.into()
                        }
                        Expr::Propagate { label: None, .. } => {
                            // we don't have to do anything because an error should've already been
                            // reported by `hir`
                            Ty::Unknown.into()
                        }
                        Expr::Propagate {
                            expr: inner,
                            label: Some(label),
                            try_range,
                        } => {
                            let inner_ty = self.tys[self.file][*inner];

                            if let Ty::Optional { sub_ty } = inner_ty.as_ref() {
                                self.break_with(
                                    *label,
                                    Some(expr),
                                    *try_range,
                                    Ty::Nil.into(),
                                    false,
                                );

                                *sub_ty
                            } else if let Ty::ErrorUnion {
                                error_ty,
                                payload_ty,
                            } = inner_ty.as_ref()
                            {
                                self.break_with(*label, Some(expr), *try_range, *error_ty, false);

                                *payload_ty
                            } else {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::PropagateNonPropagatable {
                                        found: inner_ty,
                                    },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            }
                        }
                        Expr::Directive { name, args } => {
                            let mut args = args.iter();

                            let call_range = self.bodies.range_for_expr(expr);
                            let call_end = call_range
                                .end()
                                .checked_sub(TextSize::new(1))
                                .unwrap_or(call_range.end());
                            let call_end = TextRange::new(call_end, call_end);

                            match self.interner.lookup(name.name.0) {
                                "unwrap" => 'blk: {
                                    // first arg = enum to unwrap
                                    let Some(vary_val) = args.next() else {
                                        // we could also report that a second argument of type `type`
                                        // is needed, but since that argument isn't required for
                                        // optionals I'm deciding not to
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::MissingArg {
                                                expected: ExpectedTy::SumType,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };
                                    let sum_ty = self.tys[self.file][*vary_val];
                                    if !self.expect_match(sum_ty, ExpectedTy::SumType, *vary_val) {
                                        break 'blk Ty::Unknown.into();
                                    }

                                    // second arg = variant type
                                    if let Some(variant_ty_val) = args.next() {
                                        let variant_ty = self.tys[self.file][*variant_ty_val];
                                        if !self.expect_match(
                                            variant_ty,
                                            ExpectedTy::Concrete(Ty::Type.into()),
                                            *variant_ty_val,
                                        ) {
                                            break 'blk Ty::Unknown.into();
                                        }
                                        let variant_ty = self.const_ty(*variant_ty_val)?;

                                        if !sum_ty.has_sum_variant(&variant_ty) {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::NotAVariantOfSumType {
                                                    ty: variant_ty,
                                                    sum_ty,
                                                },
                                                file: self.file,
                                                expr: Some(expr),
                                                range: self.bodies.range_for_expr(*variant_ty_val),
                                                help: None,
                                            });
                                            break 'blk Ty::Unknown.into();
                                        }

                                        let mut extra_args = false;
                                        for arg in args {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::ExtraArg {
                                                    found: self.tys[self.file][*arg],
                                                },
                                                file: self.file,
                                                expr: Some(*arg),
                                                range: self.bodies.range_for_expr(*arg),
                                                help: None,
                                            });
                                            extra_args = true;
                                        }
                                        if extra_args {
                                            break 'blk Ty::Unknown.into();
                                        }

                                        variant_ty
                                    } else if let Ty::Optional { sub_ty } = sum_ty.absolute_ty() {
                                        *sub_ty
                                    } else {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::MissingArg {
                                                expected: ExpectedTy::Concrete(Ty::Type.into()),
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        Ty::Unknown.into()
                                    }
                                }
                                "is_variant" => 'blk: {
                                    // first arg = enum to unwrap
                                    let Some(vary_val) = args.next() else {
                                        // we could also report that a second argument of type `type`
                                        // is needed, but since that argument isn't required for
                                        // optionals I'm deciding not to
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::MissingArg {
                                                expected: ExpectedTy::SumType,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };
                                    let sum_ty = self.tys[self.file][*vary_val];
                                    if !self.expect_match(sum_ty, ExpectedTy::SumType, *vary_val) {
                                        break 'blk Ty::Unknown.into();
                                    }

                                    // second arg = variant type
                                    let Some(variant_ty_val) = args.next() else {
                                        // unlike #unwrap which will work for optionals without a
                                        // second argument, #is_variant always requires a second
                                        // argument
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::MissingArg {
                                                expected: ExpectedTy::Concrete(Ty::Type.into()),
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };

                                    let variant_ty = self.tys[self.file][*variant_ty_val];
                                    if !self.expect_match(
                                        variant_ty,
                                        ExpectedTy::Concrete(Ty::Type.into()),
                                        *variant_ty_val,
                                    ) {
                                        break 'blk Ty::Unknown.into();
                                    }
                                    let variant_ty = self.const_ty(*variant_ty_val)?;

                                    if !sum_ty.has_sum_variant(&variant_ty) {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::NotAVariantOfSumType {
                                                ty: variant_ty,
                                                sum_ty,
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(*variant_ty_val),
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    }

                                    let mut extra_args = false;
                                    for arg in args {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::ExtraArg {
                                                found: self.tys[self.file][*arg],
                                            },
                                            file: self.file,
                                            expr: Some(*arg),
                                            range: self.bodies.range_for_expr(*arg),
                                            help: None,
                                        });
                                        extra_args = true;
                                    }
                                    if extra_args {
                                        break 'blk Ty::Unknown.into();
                                    }

                                    Ty::Bool.into()
                                }
                                "builtin" => 'blk: {
                                    // first arg = builtin name
                                    let Some(name_val) = args.next() else {
                                        // we could also report that a second argument of type `type`
                                        // is needed, but since that argument isn't required for
                                        // optionals I'm deciding not to
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::MissingArg {
                                                expected: ExpectedTy::Concrete(Ty::String.into()),
                                            },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };
                                    let name_ty = self.tys[self.file][*name_val];
                                    if !self.expect_match(
                                        name_ty,
                                        ExpectedTy::Concrete(Ty::String.into()),
                                        *name_val,
                                    ) {
                                        break 'blk Ty::Unknown.into();
                                    }
                                    // todo: allow this to be any const expr
                                    let hir::Expr::StringLiteral(name) = &self.bodies[*name_val]
                                    else {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::NotStringLit,
                                            file: self.file,
                                            expr: Some(*name_val),
                                            range: self.bodies.range_for_expr(*name_val),
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };

                                    let Ok(builtin) =
                                        BuiltinKind::from_str(self.interner.lookup(*name))
                                    else {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::NotABuiltin { name: *name },
                                            file: self.file,
                                            expr: Some(*name_val),
                                            range: self.bodies.range_for_expr(*name_val),
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };

                                    builtin.to_expected()
                                }
                                _ => {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::UnknownDirective {
                                            name: name.name.0,
                                        },
                                        file: self.file,
                                        expr: Some(expr),
                                        range: name.range,
                                        help: None,
                                    });

                                    Ty::Unknown.into()
                                }
                            }
                        }
                        Expr::Import(file_name) => Ty::File(*file_name).into(),
                    };

                    self.tys[self.file].expr_tys.insert(expr, ty);
                }
                Descendant::PreStmt(stmt) => {
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
                                    // note: type annotations get inserted into `expected_tys`
                                    // in a different loop at the beginning of the `infer_expr`
                                    // function

                                    let value_ty = self.tys[self.file][value];
                                    self.expect_match(
                                        value_ty,
                                        ExpectedTy::Concrete(ty_annotation),
                                        value,
                                    );
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

                            let non_mut_help = self
                                .get_mutability(assign_body.dest, true, false)
                                .into_diagnostic();

                            if non_mut_help.is_some() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::CannotMutate,
                                    file: self.file,
                                    // making expr the dest isn't technically correct, but it works
                                    expr: Some(assign_body.dest),
                                    range: assign_body.range,
                                    help: non_mut_help,
                                });
                                continue;
                            }

                            let dest_ty = self.tys[self.file][assign_body.dest];
                            let value_ty = self.tys[self.file][assign_body.value];

                            match assign_body
                                .quick_assign_op
                                .map(|op| (op, op.get_possible_output_ty(&dest_ty, &value_ty)))
                            {
                                Some((op, Some(output_ty))) => {
                                    if *dest_ty != Ty::Unknown
                                        && *value_ty != Ty::Unknown
                                        && !op.can_perform(&output_ty.max_ty)
                                    {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::BinaryOpMismatch {
                                                op,
                                                first: dest_ty,
                                                second: value_ty,
                                            },
                                            file: self.file,
                                            // making expr the dest isn't technically correct, but it works
                                            expr: Some(assign_body.dest),
                                            range: assign_body.range,
                                            help: None,
                                        });
                                    }

                                    let max_ty = output_ty.max_ty.into();

                                    self.replace_weak_tys(assign_body.dest, max_ty);
                                    self.replace_weak_tys(assign_body.value, max_ty);
                                }
                                Some((op, None)) => {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::BinaryOpMismatch {
                                            op,
                                            first: dest_ty,
                                            second: value_ty,
                                        },
                                        file: self.file,
                                        // making expr the dest isn't technically correct, but it works
                                        expr: Some(assign_body.dest),
                                        range: assign_body.range,
                                        help: None,
                                    });
                                }
                                None => {
                                    if dest_ty.is_weak_replaceable_by(&value_ty) {
                                        self.replace_weak_tys(assign_body.dest, value_ty);
                                    } else {
                                        self.expect_match(
                                            value_ty,
                                            ExpectedTy::Concrete(dest_ty),
                                            assign_body.value,
                                        );
                                    }
                                }
                            }

                            self.find_usages(&[assign_body.dest, assign_body.value], stmt);
                        }
                        Stmt::Break { label: None, .. } => {}
                        Stmt::Break {
                            label: Some(label),
                            value,
                            range,
                            ..
                        } => {
                            let value_ty = value.map_or_else(
                                || Ty::Void.into(),
                                |value| self.tys[self.file][value],
                            );

                            let range =
                                value.map_or(range, |value| self.bodies.range_for_expr(value));

                            self.break_with(label, value, range, value_ty, true);
                        }
                        Stmt::Continue { .. } => {}
                        Stmt::Defer { expr, .. } => {
                            self.find_usages(&[expr], stmt);
                        }
                    }

                    self.inferred_stmts.insert((self.file, stmt));
                }
                // Although the type is called *PostStmt*, since we reversed the list these
                // actually come *before* all their inner subexpressions.
                //
                // This is useful because inserting a value into `expected_tys` will change
                // how types get resolved and how errors get reported
                Descendant::PostStmt(stmt) => {
                    if self.inferred_stmts.contains(&(self.file, stmt)) {
                        continue;
                    }

                    match self.bodies[stmt] {
                        Stmt::Expr(expr) => {
                            self.find_usages(&[expr], stmt);
                        }
                        Stmt::LocalDef(local_def) => {
                            let def_body = &self.bodies[local_def];

                            if let Some(ty_annotation_expr) = def_body.ty
                                && let Some(value) = def_body.value
                            {
                                let ty_annotation = self.const_ty(ty_annotation_expr)?;

                                self.expected_tys.insert(
                                    value,
                                    ExprExpected {
                                        expected_ty: ty_annotation,
                                        annotation_range: self
                                            .bodies
                                            .range_for_expr(ty_annotation_expr),
                                        is_return_ty: false,
                                        is_default: false,
                                    },
                                );
                            }
                        }
                        _ => {}
                    }
                }
            };
        }

        Ok(self.tys[self.file][expr])
    }

    fn break_with(
        &mut self,
        label: ScopeId,
        value: Option<Idx<Expr>>,
        range: TextRange,
        ty: Intern<Ty>,
        replace_found_with_new_max: bool,
    ) {
        let referenced_expr = self.bodies[label];

        let must_be_void = matches!(
            self.bodies[referenced_expr],
            Expr::While {
                condition: Some(_),
                ..
            }
        );

        match self.try_get_previous_ty(referenced_expr) {
            Some(expected_ty) => {
                self.expect_block_match(
                    value,
                    ty,
                    range,
                    referenced_expr,
                    expected_ty,
                    replace_found_with_new_max,
                );
            }
            None => {
                if must_be_void && !ty.is_void() {
                    // we just checked that the type wasn't void
                    assert!(!ty.can_be_created_from_nothing());

                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::Mismatch {
                            expected: ExpectedTy::Concrete(Ty::Void.into()),
                            found: ty,
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
                    // the type just hasn't been set yet
                    self.tys[self.file].expr_tys.insert(referenced_expr, ty);
                }
            }
        }
    }

    fn try_get_previous_ty(&self, expr: Idx<Expr>) -> Option<Intern<Ty>> {
        self.tys[self.file]
            .expr_tys
            .get(expr)
            .copied()
            .or_else(|| self.expected_tys.get(expr).copied().map(|e| e.expected_ty))
    }

    /// Only call for blocks which had their type previously set by a `break`
    ///
    /// returns the max of the found expression and the current type of the block
    ///
    /// todo: what if the expected type is nil but then the block type becomes ?u64 or something
    /// like that?
    fn expect_block_match(
        &mut self,
        found_expr: Option<Idx<hir::Expr>>,
        found_ty: Intern<Ty>,
        found_range: TextRange,
        block_expr: Idx<hir::Expr>,
        block_ty: Intern<Ty>,
        replace_found_with_new_max: bool,
    ) -> Option<Intern<Ty>> {
        if found_ty.is_unknown() || block_ty.is_unknown() {
            return None;
        }

        if let Some(max) = block_ty.max(&found_ty) {
            let max = max.into();
            self.tys[self.file].expr_tys.insert(block_expr, max);
            if replace_found_with_new_max && let Some(found_expr) = found_expr {
                self.replace_weak_tys(found_expr, max);
            }

            Some(max)
        } else if found_ty.can_fit_into(&block_ty) {
            if replace_found_with_new_max && let Some(found_expr) = found_expr {
                self.replace_weak_tys(found_expr, block_ty);
            }

            Some(block_ty)
        } else {
            let help = if let Some(expected) = self.expected_tys.get(block_expr) {
                if expected.is_return_ty {
                    TyDiagnosticHelp {
                        kind: TyDiagnosticHelpKind::ReturnTyHere {
                            ty: expected.expected_ty,
                            is_default: expected.is_default,
                        },
                        range: expected.annotation_range,
                    }
                } else {
                    TyDiagnosticHelp {
                        kind: TyDiagnosticHelpKind::AnnotationHere {
                            ty: expected.expected_ty,
                        },
                        range: expected.annotation_range,
                    }
                }
            } else {
                let id = self.bodies.block_to_scope_id(block_expr).unwrap();

                let mut usages = self.bodies.scope_id_usages(id).iter();
                loop {
                    // todo: maybe use better ranges for these errors
                    match usages.next() {
                        Some(ScopeUsage::Expr(expr)) => {
                            assert!(matches!(self.bodies[*expr], hir::Expr::Propagate { .. }));

                            break TyDiagnosticHelp {
                                kind: TyDiagnosticHelpKind::PropagateHere { ty: block_ty },
                                range: self.bodies.range_for_expr(*expr),
                            };
                        }
                        Some(ScopeUsage::Stmt(stmt)) => match self.bodies[*stmt] {
                            hir::Stmt::Break {
                                is_return: false,
                                value,
                                ..
                            } => {
                                break TyDiagnosticHelp {
                                    kind: TyDiagnosticHelpKind::BreakHere {
                                        ty: block_ty,
                                        is_default: value.is_none(),
                                    },
                                    range: self.bodies.range_for_stmt(*stmt),
                                };
                            }
                            hir::Stmt::Break {
                                is_return: true,
                                value,
                                ..
                            } => {
                                break TyDiagnosticHelp {
                                    kind: TyDiagnosticHelpKind::ReturnHere {
                                        ty: block_ty,
                                        is_default: value.is_none(),
                                    },
                                    range: self.bodies.range_for_stmt(*stmt),
                                };
                            }
                            hir::Stmt::Continue { .. } => {
                                // continues can't change the type of a block, so we skip them
                            }
                            _ => {}
                        },
                        None => unreachable!(
                            "we already checked for expected_ty, so something must have previously set the block type"
                        ),
                    }
                }
            };

            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(block_ty),
                    found: found_ty,
                },
                file: self.file,
                expr: Some(found_expr.unwrap_or(block_expr)),
                range: found_range,
                help: Some(help),
            });

            // make the block type unknown so errors don't get reported twice in a row
            self.tys[self.file]
                .expr_tys
                .insert(block_expr, Ty::Unknown.into());

            None
        }
    }

    /// Used in `const_ty` to report expressions that aren't types
    fn report_non_type(&mut self, expr: Idx<hir::Expr>, expr_ty: Intern<Ty>) {
        if *expr_ty == Ty::Type {
            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::CantUseAsTy,
                file: self.file,
                expr: Some(expr),
                range: self.bodies.range_for_expr(expr),
                help: None,
            });
        } else if !expr_ty.is_unknown() {
            self.diagnostics.push(TyDiagnostic {
                kind: TyDiagnosticKind::Mismatch {
                    expected: ExpectedTy::Concrete(Ty::Type.into()),
                    found: expr_ty,
                },
                file: self.file,
                expr: Some(expr),
                range: self.bodies.range_for_expr(expr),
                help: None,
            });
        }
    }

    /// If found does not match expected, an error is thrown at the expression
    ///
    /// This function will also do weak type replacing
    pub(crate) fn expect_match(
        &mut self,
        found: Intern<Ty>,
        expected: ExpectedTy,
        expr: Idx<hir::Expr>,
    ) -> bool {
        // if the expression we're checking against is an
        // int literal (which can be inferred into any int type),
        // then we can just quickly set it's type here
        if let (hir::Expr::IntLiteral(num), Some(Ty::IInt(_)) | Some(Ty::UInt(_))) =
            (&self.bodies[expr], expected.get_concrete().as_deref())
        {
            let expected = expected.get_concrete().expect("already checked for Some");

            self.tys[self.file].expr_tys[expr] = expected;

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

        // todo: make sure this works for blocks
        if expected.get_concrete().is_some_and(|ty| *ty == Ty::Type) && found.is_zero_sized() {
            return true;
        }

        if found.is_unknown()
            || expected
                .get_concrete()
                .as_deref()
                .is_some_and(Ty::is_unknown)
        {
            // return false without throwing an error
            return false;
        }

        if expected.can_take(&found) {
            if let ExpectedTy::Concrete(expected_ty) = expected {
                self.replace_weak_tys(expr, expected_ty);
            }

            true
        } else {
            if let ExpectedTy::Concrete(expected_ty) = expected {
                assert!(
                    !found.is_weak_replaceable_by(&expected_ty),
                    "`is_weak_replaceable_by` is not a subset of `can_fit_into` for `{}` -> `{}`\n(`is_weak_replaceable_by` returned true but `can_fit_into` returned false)",
                    found.simple_display(self.interner, true),
                    expected_ty.simple_display(self.interner, true),
                );
            }

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
                                expected: ExpectedTy::Concrete(Ty::Type.into()),
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

                if actual_ty.can_have_a_name() {
                    set_type_name(actual_ty, TyName::Global(fqn));
                }

                Ok(actual_ty)
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

        let descendants = self
            .bodies
            .descendants(
                expr,
                hir::DescentOpts::Types {
                    include_local_value: &include_local_value,
                },
            )
            .collect_vec();

        // println!("CONST TYPE\n{descendants:#?}");

        for descendant in descendants.into_iter().rev() {
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
                                self.report_non_type(expr, local_ty);
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
                        Expr::Member { previous, name } => {
                            // todo: remove recursion

                            // this has to be done because `infer_fqn` will call
                            // `const_ty` on the type annotation of the fqn, even
                            // though it hasn't been processed by `infer_expr` yet
                            let previous_ty = self.infer_expr(*previous)?;

                            match previous_ty.as_ref() {
                                Ty::File(file) => self.fqn_to_ty(
                                    hir::Fqn {
                                        file: *file,
                                        name: name.name,
                                    },
                                    Some(*previous),
                                    expr,
                                    name.range,
                                )?,
                                Ty::Type => {
                                    // todo: remove recursion
                                    // println!("ty get #{}", previous.into_raw());
                                    // let const_ty =
                                    //     self.tys[self.file].get_meta_ty(*previous).unwrap();
                                    let const_ty = self.const_ty(*previous)?;
                                    match const_ty.as_ref() {
                                        Ty::Enum { variants, .. } => variants
                                            .iter()
                                            .find(|variant| {
                                                let Ty::EnumVariant { variant_name, .. } =
                                                    variant.as_ref()
                                                else {
                                                    unreachable!(
                                                        "all variants should be `Ty::Variant`"
                                                    );
                                                };

                                                *variant_name == name.name
                                            })
                                            .copied()
                                            .unwrap_or_else(|| {
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::NotAShorthandVariantOfSumType {
                                                        ty: name.name.0,
                                                        sum_ty: const_ty,
                                                    },
                                                    file: self.file,
                                                    expr: Some(expr),
                                                    range: self.bodies.range_for_expr(expr),
                                                    help: None,
                                                });

                                                Ty::Unknown.into()
                                            }),
                                        _ => {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::CantUseAsTy,
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
                                    // todo: remove recursion
                                    let expr_ty = self.infer_expr(expr)?;

                                    self.report_non_type(expr, expr_ty);

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
                                let usize_ty = Ty::UInt(u8::MAX).into();
                                if !self.expect_match(
                                    self.tys[self.file][*size],
                                    ExpectedTy::Concrete(usize_ty),
                                    *size,
                                ) {
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
                                    Some(ComptimeResult::Integer { num, .. }) => {
                                        Ty::ConcreteArray { size: num, sub_ty }.into()
                                    }
                                    _ => {
                                        // todo: we check that the array size is a `usize` above,
                                        // soo... is this even reachable?
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
                            uid: *uid,
                            sub_ty: self.tys[self.file].meta_tys[*ty],
                        }
                        .into(),
                        Expr::StructDecl { uid, members } => Ty::ConcreteStruct {
                            uid: *uid,
                            members: members
                                .iter()
                                .cloned()
                                .filter_map(|hir::MemberDecl { name, ty }| {
                                    name.map(|name| MemberTy {
                                        name: name.name,
                                        ty: self.tys[self.file].meta_tys[ty],
                                    })
                                })
                                .collect(),
                        }
                        .into(),
                        Expr::EnumDecl {
                            uid: enum_uid,
                            variants,
                        } => {
                            let mut variant_tys = Vec::with_capacity(variants.len());

                            let mut used_discriminants =
                                FxHashSet::with_capacity_and_hasher(variants.len(), FxBuildHasher);
                            let mut manual_discriminants =
                                FxHashMap::with_capacity_and_hasher(variants.len(), FxBuildHasher);

                            manual_discriminants.values();

                            // first figure out the discriminants, then figure out the final types

                            for (idx, variant) in variants.iter().enumerate() {
                                if variant.name.is_none() {
                                    continue;
                                }

                                if let Some(discrim_expr) = variant.discriminant {
                                    'discrim_calc: {
                                        let ty_u8 = Ty::UInt(8).into();

                                        // we must infer it manually because it might not
                                        // have been inferred.
                                        if !self.expect_match(
                                            self.tys[self.file][discrim_expr],
                                            ExpectedTy::Concrete(ty_u8),
                                            discrim_expr,
                                        ) {
                                            break 'discrim_calc;
                                        }

                                        self.replace_weak_tys(discrim_expr, ty_u8);

                                        let expr_const = self.get_const(discrim_expr);
                                        if !expr_const.is_const() {
                                            println!("not const {expr_const:?}");
                                            if expr_const.should_report_not_const() {
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::DiscriminantNotConst,
                                                    file: self.file,
                                                    range: self.bodies.range_for_expr(discrim_expr),
                                                    expr: Some(discrim_expr),
                                                    help: None,
                                                });
                                            }
                                            break 'discrim_calc;
                                        }

                                        match self.const_data(self.file, discrim_expr)? {
                                            Some(ComptimeResult::Integer { num, .. }) => {
                                                if used_discriminants.contains(&num) {
                                                    self.diagnostics.push(TyDiagnostic {
                                                        kind: TyDiagnosticKind::DiscriminantUsedAlready {
                                                            value: num
                                                        },
                                                        file: self.file,
                                                        range: self
                                                            .bodies
                                                            .range_for_expr(discrim_expr),
                                                        expr: Some(discrim_expr),
                                                        help: None,
                                                    })
                                                } else {
                                                    used_discriminants.insert(num);
                                                    manual_discriminants.insert(idx, num);
                                                }
                                            }
                                            _ => {
                                                // todo: we check that the discriminant is a `usize` above,
                                                // soo... is this even reachable?
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::DiscriminantNotInt,
                                                    file: self.file,
                                                    range: self.bodies.range_for_expr(discrim_expr),
                                                    expr: Some(discrim_expr),
                                                    help: None,
                                                });
                                            }
                                        }
                                    }
                                }
                            }

                            let mut latest_discrim = 0;

                            for (idx, variant) in variants.iter().enumerate() {
                                let Some(name) = variant.name else {
                                    continue;
                                };

                                let sub_ty = variant.ty.map_or_else(
                                    || Ty::Void.into(),
                                    |ty| self.tys[self.file].meta_tys[ty],
                                );

                                let discriminant = match manual_discriminants.get(&idx) {
                                    Some(discrim) => *discrim,
                                    None => {
                                        let mut discrim = latest_discrim;
                                        while used_discriminants.contains(&discrim) {
                                            discrim += 1;
                                        }
                                        discrim
                                    }
                                };

                                if discriminant >= latest_discrim {
                                    latest_discrim = discriminant + 1;
                                }

                                variant_tys.push(
                                    Ty::EnumVariant {
                                        enum_uid: *enum_uid,
                                        variant_name: name.name,
                                        uid: variant.uid,
                                        sub_ty,
                                        discriminant,
                                    }
                                    .into(),
                                );
                            }

                            let enum_ty = Ty::Enum {
                                uid: *enum_uid,
                                variants: variant_tys,
                            }
                            .into();

                            ty::set_enum_uid(*enum_uid, enum_ty);

                            enum_ty
                        }
                        Expr::OptionalDecl { ty } => Ty::Optional {
                            sub_ty: self.tys[self.file].meta_tys[*ty],
                        }
                        .into(),
                        Expr::ErrorUnionDecl {
                            error_ty,
                            payload_ty,
                        } => {
                            let error_ty = self.tys[self.file].meta_tys[*error_ty];
                            let payload_ty = self.tys[self.file].meta_tys[*payload_ty];

                            if !error_ty.can_differentiate_from(&payload_ty) {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::ImpossibleToDifferentiateErrorUnion {
                                        error_ty,
                                        payload_ty,
                                    },
                                    file: self.file,
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            } else {
                                Ty::ErrorUnion {
                                    error_ty,
                                    payload_ty,
                                }
                                .into()
                            }
                        }
                        Expr::Lambda(lambda) => {
                            let hir::Lambda {
                                params,
                                return_ty,
                                body,
                                ..
                            } = &self.bodies[*lambda];

                            let return_ty = if let Some(return_ty) = return_ty {
                                self.tys[self.file].meta_tys[*return_ty]
                            } else {
                                Ty::Void.into()
                            };

                            let mut param_tys = Vec::with_capacity(params.len());

                            for (idx, param) in params.iter().enumerate() {
                                let mut ty = self.tys[self.file].meta_tys[param.ty];

                                let mut impossible_to_differentiate = false;
                                if let Some(last_param) = idx
                                    .checked_sub(1)
                                    .and_then(|idx| params.get(idx))
                                    .filter(|p| p.varargs)
                                {
                                    let last_ty = self.tys[self.file].meta_tys[last_param.ty];

                                    if !ty.can_differentiate_from(&last_ty) {
                                        impossible_to_differentiate = true;
                                        self.diagnostics.push(TyDiagnostic {
                                            kind:
                                                TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                                                    previous_ty: last_ty,
                                                    current_ty: ty,
                                                },
                                            file: self.file,
                                            expr: Some(expr),
                                            range: param.range,
                                            help: None,
                                        });
                                    }
                                }

                                if param.varargs {
                                    ty = Ty::Slice { sub_ty: ty }.into();
                                }

                                param_tys.push(ParamTy {
                                    ty,
                                    varargs: param.varargs,
                                    impossible_to_differentiate,
                                });
                            }

                            let ty = Ty::Function {
                                param_tys,
                                return_ty,
                            }
                            .into();

                            // if the function has a body then it isn't a type
                            if *body != hir::LambdaBody::Empty {
                                self.report_non_type(expr, ty);

                                Ty::Unknown.into()
                            } else {
                                ty
                            }
                        }
                        Expr::Comptime(comptime) => {
                            let hir::Comptime { body } = self.bodies[*comptime];

                            let ty = self.tys[self.file][body];

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
                            self.tys[self.file].get_meta_ty(*paren_expr).unwrap()
                        }
                        _ => {
                            // TODO: remove recursion
                            let expr_ty = self.infer_expr(expr)?;

                            if expr_ty.is_zero_sized() {
                                println!(
                                    "converting #{} ({:?}) into a const `{}` type",
                                    expr.into_raw(),
                                    self.bodies[expr],
                                    expr_ty.simple_display(self.interner, true),
                                );
                                expr_ty
                            } else {
                                self.report_non_type(expr, expr_ty);

                                Ty::Unknown.into()
                            }
                        }
                    };

                    self.tys[self.file].meta_tys.insert(expr, ty);
                }
                Descendant::PreStmt(_) => unreachable!(),
                Descendant::PostStmt(_) => unreachable!(),
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

                // todo: remove recursion
                self.const_data(file, self.world_bodies.body(fqn))
            }
            Expr::Member {
                previous,
                name: field,
            } => match self.tys[self.file][*previous].as_ref() {
                Ty::File(file) => {
                    let fqn = hir::Fqn {
                        file: *file,
                        name: field.name,
                    };

                    // todo: remove recursion
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
            self.currently_inferring,
            self.bodies
                .descendants(
                    expr,
                    hir::DescentOpts::All {
                        include_lambdas: false,
                        include_post_stmts: false,
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
        checked.insert(self.currently_inferring);

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
                        Expr::Switch { .. } => {}
                        Expr::Local(_) => {}
                        Expr::SwitchArgument(_) => {}
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
                                            include_post_stmts: false,
                                        },
                                    )
                                    .collect(),
                            ));
                        }
                        Expr::Param { .. } => {}
                        Expr::Member {
                            previous,
                            name: field,
                        } => {
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
                                                        include_post_stmts: false,
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

                            if lambda_body.body == hir::LambdaBody::Empty
                                && lambda_body.return_ty.is_none()
                            {
                                return Ok(false);
                            }

                            // println!(
                            //     "lambda #{} : {} {}",
                            //     expr.into_raw(),
                            //     lambda_body.is_extern,
                            //     is_type
                            // );

                            if let hir::LambdaBody::Block(block) = lambda_body.body {
                                checking_stack.push((
                                    lambda,
                                    self.world_bodies[file]
                                        .descendants(
                                            block,
                                            hir::DescentOpts::All {
                                                include_lambdas: false,
                                                include_post_stmts: false,
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
                        Expr::EnumDecl { .. } => {}
                        Expr::Nil => {}
                        Expr::OptionalDecl { .. } => {}
                        Expr::ErrorUnionDecl { .. } => {}
                        Expr::Propagate { .. } => {}
                        Expr::Import(_) => {}
                        Expr::Directive { .. } => {}
                    }
                }
                Descendant::PreStmt(stmt) => match &self.world_bodies[file][stmt] {
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
                Descendant::PostStmt(_) => unreachable!(),
            }
        }

        Ok(true)
    }
}

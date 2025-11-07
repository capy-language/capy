use std::{collections::HashSet, str::FromStr};

use debug::debug;
use hir::{
    ArmVariant, Descendant, Expr, LocalDef, MemberLiteral, ScopeId, ScopeUsage, Stmt, common::*,
};
use indexmap::IndexMap;
use interner::Interner;
use internment::Intern;
use itertools::Itertools;
use la_arena::{Arena, ArenaMap, Idx, IdxRange};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use text_size::{TextRange, TextSize};
use topo::TopoSort;

use crate::{
    AreaTys, BuiltinKind, EvalComptimeFn, ExpectedTy, InferResult, NaiveLookupErr, TyDiagnostic,
    TyDiagnosticHelp, TyDiagnosticHelpKind, TyDiagnosticKind, WorldTys,
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

struct TypedLambdaHeaders {
    param_tys: Vec<ParamTy>,
    return_ty: Intern<Ty>,
    any_comptime: bool,
    is_type: bool,
}

/// This is used when `infer_lambda_headers` needs the comptime args in order to evaluate
/// the types of the headers.
#[derive(Debug)]
struct RequiresComptimeArgs;

/// This is used by `evaluate_comptime_args` when there are errors in the arguments which prevent
/// them from being evaluated
#[derive(Debug)]
struct ArgsContainDiagnostics;

/// Note: this is "global" as in "global variable,"
/// not global as in "including everything from all over the project".
///
/// the project-wide struct which holds context for resolving type information
/// is `ProjectInferenceCtx`
///
/// Even though this is called "ctx," it's extremely impermanent, and will be
/// very likely destroyed even in the middle of a global being resolved.
///
/// see the comment on `inferred_stmts`
pub(crate) struct GlobalInferenceCtx<'a> {
    /// This is the TypedFqn we are currently inside of,
    /// even if it's not the actual body we're resolving.
    /// This could be because of several layers of lambdas within a global function.
    pub(crate) loc: ConcreteLoc,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) world_bodies: &'a hir::WorldBodies,
    pub(crate) bodies: &'a hir::Bodies,
    pub(crate) interner: &'a Interner,
    /// This is used primarily by blocks so that e.g. if a block is not expected to be anything,
    /// returned values of `str` and `u64` will cause a type mismatch error to be reported.
    /// But if a block is expected to be `str!u64` (via a type annotation or return type),
    /// returned values of `str` and `u64` will combine to `str!u64` and there will be no error
    pub(crate) expected_tys: ArenaMap<Idx<hir::Expr>, ExprExpected>,
    // todo: what happens to this when an uninferred global is reached?
    // should this be stored in `ProjectInferenceCtx`?
    pub(crate) local_usages: ArenaMap<Idx<hir::LocalDef>, FxHashSet<Idx<hir::Stmt>>>,
    /// this is just an arena that physically stores the compile-time results
    /// associated with each comptime argument in a generic function call.
    pub(crate) generics_arena: &'a mut Arena<ComptimeResult>,
    /// this is the map that associates each call expression with a range of comptime results
    /// in the above arena.
    ///
    /// These are stored so that the "second stage" of Expr::Call (see infer_expr) will know
    /// to activate
    pub(crate) call_associated_generics: &'a mut FxHashMap<(ConcreteLoc, Idx<Expr>), ComptimeArgs>,
    /// this is used because the way `infer_stmt` and `infer_expr` operate is that
    /// they can run multiple times in a row. In a way it's similar to how async works
    /// under the hood. Both functions are state machines that will return to the operator
    /// if they encounter another global that hasn't been resolved yet.
    ///
    /// The operator will then make sure that the "dependency" is resolved first before trying
    /// to to resolve this global again.
    ///
    /// These dependencies are found *during* expression and statment inference, which means
    /// that the operator will start inferring global A, then it returns because it has to
    /// infer dependency B, then the operator starts with A again, then it has to stop again,
    /// and so on.
    ///
    /// This means that the first expressions and statements in a global will be gone over
    /// many times in a row while the function is getting back to where it was the last time.
    ///
    /// For expressions it's easy to figure out what's already been done because one can simply
    /// check `tys[global_location].expr_tys`, but statments don't really have "types."
    ///
    /// So I just mark statements in this hashset when I'm done resolving them.
    ///
    /// Probably isn't the most efficient way to do it, but this crate is already so complex that I didn't
    /// want to implement ANOTHER function that analyzes the graph for some other obscure reason.
    ///
    /// TODO: make this a local struct instead of a reference, and make it just Idx<hir::Stmt>
    pub(crate) inferred_stmts: &'a mut FxHashSet<(ConcreteLoc, Idx<hir::Stmt>)>,
    pub(crate) tys: &'a mut WorldTys,
    /// This has values if self.loc is a ConcreteLambdaLoc
    pub(crate) param_tys: Vec<ParamTy>,
    /// This stores the current comptime args while evaluating the headers of a lambda.
    /// These may or may not be the comptime args stored in self.loc
    ///
    /// This is updated in-place, so later arguments may depend on the comptime value
    /// of earlier arguments
    /// TODO: test that
    pub(crate) inline_comptime_args: Vec<Idx<ComptimeResult>>,
    /// Unlike `inline_comptime_args`, this doesn't store ALL the results all at once.
    /// it is updated in place, as the parameters are typed, and then cleared after
    /// the lambda headers have been fully typed
    pub(crate) inline_comptime_tys: Vec<Intern<Ty>>,
    pub(crate) all_finished_locations: &'a FxHashSet<ConcreteLoc>,
    pub(crate) to_infer: &'a mut TopoSort<ConcreteLoc>,
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
                file: self.loc.file(),
                range: self.bodies.range_for_expr(body),
                expr: Some(body),
                help: None,
            });

            // println!("not const: {:#?}", &self.bodies[body]);
        }

        assert!(self.inline_comptime_args.is_empty());
        assert!(self.inline_comptime_tys.is_empty());

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
                            self.tys[self.loc]
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

        // `or_insert` happens in the following case:
        // ```
        // foo :: (comptime T: type) {
        //     x: T;
        // }
        // ```
        // when T is evaluated it will go through `expect_match`
        // which will send it to here, despite the fact it doesn't
        // actually have an entry in expr_tys.
        let found_ty = *self.tys[self.loc].expr_tys.entry(expr).or_insert(new_ty);

        let mut really_replaced = true;

        if !found_ty.is_weak_replaceable_by(&new_ty) {
            return false;
        }

        assert!(
            found_ty.can_fit_into(&new_ty),
            "`is_weak_replaceable_by` is not a subset of `can_fit_into` for `{}` -> `{}`\n(`is_weak_replaceable_by` returned true but `can_fit_into` returned false)",
            found_ty.debug(self.interner, true),
            new_ty.debug(self.interner, true),
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
        //     self.loc.debug(self.interner),
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

        self.tys[self.loc].expr_tys.insert(expr, new_ty);

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
                            file: self.loc.file(),
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

                    self.tys[self.loc].expr_tys.insert(expr, new_ty);

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
                let mutable = self.tys[self.loc].expr_tys[expr]
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

                self.tys[self.loc].expr_tys.insert(
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
                        self.tys[self.loc].local_tys.insert(local_def, new_ty);
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
                let member_tys: FxHashMap<Name, Intern<Ty>> = new_ty
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
        let mut to_check = vec![(self.loc, expr)];

        let mut idx = 0;
        while let Some((loc, expr)) = to_check.get(idx).copied() {
            let result = match &self.world_bodies[loc.file()][expr] {
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
                Expr::ArrayLiteral { items, .. } if self.tys[loc][expr].is_array() => {
                    to_check.extend(items.iter().map(|e| (loc, *e)));
                    ExprIsConst::Const
                }
                Expr::LocalGlobal(global) => {
                    let new_naive = NaiveGlobalLoc {
                        file: loc.file(),
                        name: global.name,
                    };

                    assert!(!self.world_bodies.has_polymorphic_body(new_naive.wrap()));
                    let new_loc = new_naive.make_concrete(None);

                    if self.world_bodies.global_is_extern(new_loc.to_naive()) {
                        ExprIsConst::Runtime
                    } else {
                        if !self.all_finished_locations.contains(&new_loc.wrap()) {
                            // this can only happen if there's been a cyclic error
                            assert_eq!(*self.tys.sig(new_loc.wrap()), Ty::NotYetResolved);
                            return ExprIsConst::Unknown;
                        }

                        to_check.push((
                            new_loc.wrap(),
                            self.world_bodies.global_body(new_loc.to_naive()),
                        ));
                        ExprIsConst::Const
                    }
                }
                Expr::Local(local) => {
                    let local_def = &self.world_bodies[loc.file()][*local];

                    if let Some(value) = local_def.value {
                        to_check.push((loc, value));
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
                    let old_tfqn = loc;

                    if let Ty::File(file) = self.tys[old_tfqn][*previous].as_ref() {
                        to_check.push((old_tfqn, *previous));

                        let new_loc = Fqn {
                            file: *file,
                            name: field.name,
                        };

                        if !self.world_bodies.global_exists(new_loc) {
                            ExprIsConst::Unknown
                        } else if self.world_bodies.global_is_extern(new_loc) {
                            ExprIsConst::Runtime
                        } else {
                            assert!(!self.world_bodies.has_polymorphic_body(new_loc.wrap()));
                            let new_loc = new_loc.make_concrete(None);

                            if !self.all_finished_locations.contains(&new_loc.wrap()) {
                                // this can only happen if there's been a cyclic error
                                assert_eq!(*self.tys.sig(new_loc.wrap()), Ty::NotYetResolved);
                                return ExprIsConst::Unknown;
                            }

                            to_check.push((
                                new_loc.wrap(),
                                self.world_bodies.global_body(new_loc.to_naive()),
                            ));
                            ExprIsConst::Const
                        }
                    } else {
                        ExprIsConst::Runtime
                    }
                }
                Expr::ComptimeParam { .. } => ExprIsConst::Const,
                _ => {
                    if matches!(*(self.tys[loc][expr]), Ty::Type | Ty::File(_)) {
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
                deref || self.tys[self.loc][*array].is_pointer(),
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
                let fqn = Fqn {
                    file: self.loc.file(),
                    name: name.name,
                };

                ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
            }
            Expr::Member {
                previous,
                name: field,
            } => {
                let previous_ty = self.tys[self.loc][*previous];
                match previous_ty.as_ref() {
                    Ty::File(file) => {
                        let fqn = Fqn {
                            file: *file,
                            name: field.name,
                        };

                        if *file == self.loc.file() {
                            ExprMutability::ImmutableGlobal(self.world_index.range_info(fqn).whole)
                        } else {
                            ExprMutability::ImmutableGlobal(field.range)
                        }
                    }
                    _ if deref => {
                        let path_ty = &self.tys[self.loc][expr];

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
                let ty = self.tys[self.loc][expr];

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
                    Descendant::PreExpr(expr) => match self.bodies[expr] {
                        Expr::Local(local) => Some(local),
                        _ => None,
                    },
                    Descendant::PostExpr(_) => unreachable!(),
                    Descendant::PreStmt(_) => None,
                    Descendant::PostStmt(_) => unreachable!(),
                }),
        );
    }

    fn reinfer_expr(&mut self, expr: Idx<hir::Expr>) -> Intern<Ty> {
        let previous_ty = self.tys[self.loc][expr];
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
                        hir::Expr::Propagate { expr, .. } => ctx.tys[ctx.loc][expr]
                            .propagated_ty()
                            .expect("there should be a propagated type"),
                        _ => unreachable!(),
                    },
                    ScopeUsage::Stmt(stmt) => match ctx.bodies[*stmt] {
                        hir::Stmt::Break {
                            value: Some(value), ..
                        } => ctx.tys[ctx.loc][value],
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
                        ctx.loc.debug(ctx.interner),
                        expr.into_raw(),
                        previous_ty.debug(ctx.interner, true),
                        new_ty.debug(ctx.interner, true)
                    );
                }

                // println!(
                //     "{} #{} : replacing {:?} with {:?}",
                //     self.loc.debug(self.interner),
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
                    include_post_exprs: false,
                    include_post_stmts: false,
                },
            )
            .collect_vec()
            .into_iter()
            .rev()
        {
            match next {
                Descendant::PreExpr(expr) => {
                    let previous_ty = self.tys[self.loc]
                        .expr_tys
                        .get(expr)
                        .copied()
                        .unwrap_or_else(|| {
                            panic!(
                                "{} #{} : TYPE DOES NOT EXIST",
                                self.loc.debug(self.interner),
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
                            let inner_ty = self.tys[self.loc][*inner];

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
                            let inner_ty = self.tys[self.loc][*pointer];

                            inner_ty
                                .as_pointer()
                                .map(|(_, sub_ty)| sub_ty)
                                .unwrap_or_else(|| Ty::Unknown.into())
                        }
                        Expr::Binary { lhs, rhs, op } => {
                            let lhs_ty = self.tys[self.loc][*lhs];
                            let rhs_ty = self.tys[self.loc][*rhs];

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
                            let inner_ty = self.tys[self.loc][*inner];
                            if op.can_perform(&inner_ty) {
                                op.get_possible_output_ty(inner_ty)
                            } else {
                                op.default_ty().into()
                            }
                        }
                        Expr::Index { source, .. } => {
                            let mut source_ty = self.tys[self.loc][*source];

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
                            let tail_ty = tail_expr.map(|tail_expr| self.tys[self.loc][tail_expr]);

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
                            let body_ty = self.tys[self.loc][*body];

                            if let Some(else_branch) = else_branch {
                                let new_else = self.tys[self.loc][*else_branch];

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
                        Expr::Local(local) => self.tys[self.loc].local_tys[*local],
                        Expr::Member {
                            previous,
                            name: field,
                        } => {
                            // make sure this matches up with the one in infer_expr
                            let super_ty = self.tys[self.loc][*previous];
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
                        self.tys[self.loc].expr_tys.insert(expr, new_ty);
                    }
                }
                Descendant::PostExpr(_) => unreachable!(),
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

                        let previous_ty = self.tys[self.loc][*local_def];
                        let new_ty = self.tys[self.loc][value];

                        if should_actually_replace(self, expr, previous_ty, new_ty) {
                            self.tys[self.loc].local_tys.insert(*local_def, new_ty);
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

        self.tys[self.loc][expr]
    }

    // This function is indent hell but it's worth it to make it stack overflow free
    pub(crate) fn infer_expr(&mut self, expr: Idx<Expr>) -> InferResult<Intern<Ty>> {
        if let (Some(ty), None) = (
            self.tys[self.loc].expr_tys.get(expr),
            self.bodies.block_to_scope_id(expr),
        ) {
            return Ok(*ty);
        }

        let descendants = self
            .bodies
            .descendants(
                expr,
                hir::DescentOpts::Infer {
                    include_post_exprs: false,
                    include_post_stmts: true,
                },
            )
            .collect_vec();

        // let mut res = String::new();
        // hir::debug_descendants(
        //     &mut res,
        //     self.bodies,
        //     descendants.iter().rev().copied(),
        //     false,
        //     true,
        // );
        // debug!("INFER EXPR {}\n{res}", self.loc.debug(self.interner));

        // ..., 357, 61

        // This works without recursion because children will ALWAYS come before parents
        for descendant in descendants.into_iter().rev() {
            match descendant {
                Descendant::PreExpr(expr) => {
                    if self.tys[self.loc].expr_tys.contains_idx(expr)
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
                                let item_ty = self.tys[self.loc][*item];
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
                                let item_ty = self.tys[self.loc][*item];

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
                                                                file: self.loc.file(),
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
                            let source_ty = self.tys[self.loc][*source];
                            // because it's annoying to do `foo^[0]`, this code lets you do `foo[0]`
                            let mut deref_source_ty = source_ty;
                            while let Some((_, sub_ty)) = deref_source_ty.as_pointer() {
                                deref_source_ty = sub_ty;
                            }

                            let index_ty = self.tys[self.loc][*index];

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
                                    file: self.loc.file(),
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
                                            file: self.loc.file(),
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
                                    file: self.loc.file(),
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
                                        file: self.loc.file(),
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
                            let cast_from = self.tys[self.loc][*sub_expr];

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
                                            file: self.loc.file(),
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
                            let inner_ty = self.tys[self.loc][*inner];

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
                                            file: self.loc.file(),
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
                            let deref_ty = self.tys[self.loc][*pointer];

                            match *deref_ty {
                                Ty::RawPtr { .. } => {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::DerefRaw,
                                        file: self.loc.file(),
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
                                            file: self.loc.file(),
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
                            let lhs_ty = self.tys[self.loc][*lhs];
                            let rhs_ty = self.tys[self.loc][*rhs];

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
                                        file: self.loc.file(),
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
                                    file: self.loc.file(),
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                op.default_ty().into()
                            }
                        }
                        Expr::Unary { expr, op } => {
                            let expr_ty = self.tys[self.loc][*expr];

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
                                    file: self.loc.file(),
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
                            Some(expr) => self.tys[self.loc][*expr],
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
                                            && *self.tys[self.loc][*expr] == Ty::AlwaysJumps =>
                                    {
                                        no_eval = true
                                    }
                                    _ => {}
                                }
                            }

                            match tail_expr {
                                Some(tail) => {
                                    let tail_ty = self.tys[self.loc][*tail];

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
                                                //     self.loc.debug(self.interner),
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
                                            //     self.loc.debug(self.interner),
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
                            let cond_ty = self.tys[self.loc][*condition];
                            self.expect_match(
                                cond_ty,
                                ExpectedTy::Concrete(Ty::Bool.into()),
                                *condition,
                            );

                            let body_ty = self.tys[self.loc][*body];

                            if let Some(else_branch) = else_branch {
                                let else_ty = self.tys[self.loc][*else_branch];

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
                                        file: self.loc.file(),
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
                                        file: self.loc.file(),
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
                                let cond_ty = self.tys[self.loc][*condition];
                                self.expect_match(
                                    cond_ty,
                                    ExpectedTy::Concrete(Ty::Bool.into()),
                                    *condition,
                                );
                            }
                            let body_ty = self.tys[self.loc][*body];
                            self.expect_match(
                                body_ty,
                                ExpectedTy::Concrete(Ty::Void.into()),
                                *body,
                            );

                            if let Some(previous_ty) = self.tys[self.loc].expr_tys.get(expr) {
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
                            let scrutinee_ty = self.tys[self.loc][*scrutinee];

                            if !self.expect_match(scrutinee_ty, ExpectedTy::SumType, *scrutinee) {
                                break 'switch Ty::Unknown.into();
                            }

                            // resolve all arm types beforehand
                            let mut type_resolution_error = false;
                            for arm in arms {
                                match arm.variant {
                                    Some(ArmVariant::FullyQualified(ty)) => {
                                        if !self.expect_match(
                                            self.tys[self.loc][ty],
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
                                                file: self.loc.file(),
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
                                                file: self.loc.file(),
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
                                fn matches_arm(&self, tys: &AreaTys, variant: ArmVariant) -> bool {
                                    match variant {
                                        ArmVariant::FullyQualified(ty) => {
                                            self.variant_ty == tys.meta_ty(ty).expect("all the arms should be resolved before calling `matches_arm`")
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
                                    .find(|v| v.matches_arm(&self.tys[self.loc], variant))
                                else {
                                    unreachable!()
                                };

                                if arm_variant.included_in_switch {
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::SwitchAlreadyCoversVariant {
                                            ty: arm_variant.variant_ty,
                                        },
                                        file: self.loc.file(),
                                        expr: Some(expr),
                                        range: arm.variant_range,
                                        help: None, // todo: show the previous arm
                                    });
                                } else {
                                    // if any variants haven't been covered an error will be reported
                                    arm_variant.included_in_switch = true;
                                }

                                let found_arm_ty = self.tys[self.loc][arm.body];

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
                                                file: self.loc.file(),
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
                                let default_ty = self.tys[self.loc][default.body];

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
                                                file: self.loc.file(),
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
                                        file: self.loc.file(),
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
                        Expr::Local(local) => self.tys[self.loc].local_tys[*local],
                        Expr::SwitchArgument(switch_local) => 'switch_arg: {
                            if let Some(ty) = self.tys[self.loc].switch_local_tys.get(*switch_local)
                            {
                                break 'switch_arg *ty;
                            }

                            let switch_local_body = &self.bodies[*switch_local];
                            let scrutinee_ty = self.tys[self.loc][switch_local_body.scrutinee];
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

                            self.tys[self.loc]
                                .switch_local_tys
                                .insert(*switch_local, variant_ty);

                            variant_ty
                        }
                        Expr::Param { idx, .. } | Expr::ComptimeParam { real_idx: idx, .. } => {
                            self.param_tys[*idx as usize].ty
                        }
                        Expr::InlineParam {
                            comptime_idx: idx, ..
                        } => self.inline_comptime_tys[*idx as usize],
                        Expr::LocalGlobal(name) => 'local_global: {
                            let fqn = Fqn {
                                file: self.loc.file(),
                                name: name.name,
                            };

                            let sig = match self.tys.try_naive(fqn.wrap(), &self.world_bodies) {
                                Ok(sig) => sig,
                                Err(NaiveLookupErr::NotFound) => {
                                    assert!(!self.world_bodies.has_polymorphic_body(fqn.wrap()));
                                    return Err(vec![fqn.make_concrete(None).wrap()]);
                                }
                                Err(NaiveLookupErr::IsPolymorphic) => {
                                    break 'local_global Ty::NaivePolymorphicFunction {
                                        fn_loc: fqn.wrap(),
                                    }
                                    .into();
                                }
                            };

                            if *sig == Ty::NotYetResolved {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::NotYetResolved { fqn },
                                    file: self.loc.file(),
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });

                                Ty::Unknown.into()
                            } else {
                                sig
                            }
                        }
                        Expr::Member {
                            previous,
                            name: field,
                        } => {
                            // make sure this matches up with the one in reinfer_expr
                            let super_ty = self.tys[self.loc][*previous];
                            match super_ty.as_ref() {
                                Ty::File(file) => {
                                    let fn_loc = Fqn {
                                        file: *file,
                                        name: field.name,
                                    };

                                    match self.world_index.definition(fn_loc) {
                                        hir::DefinitionStatus::Defined => {
                                            let sig = match self
                                                .tys
                                                .try_naive(fn_loc.wrap(), self.world_bodies)
                                            {
                                                Ok(sig) => sig,
                                                Err(NaiveLookupErr::NotFound) => {
                                                    return Err(vec![
                                                        fn_loc.make_concrete(None).wrap(),
                                                    ]);
                                                }
                                                Err(NaiveLookupErr::IsPolymorphic) => {
                                                    Ty::NaivePolymorphicFunction {
                                                        fn_loc: fn_loc.wrap(),
                                                    }
                                                    .into()
                                                }
                                            };

                                            if *sig == Ty::NotYetResolved {
                                                self.diagnostics.push(TyDiagnostic {
                                                    kind: TyDiagnosticKind::NotYetResolved {
                                                        fqn: fn_loc,
                                                    },
                                                    file: self.loc.file(),
                                                    expr: Some(expr),
                                                    range: self.bodies.range_for_expr(expr),
                                                    help: None,
                                                });

                                                Ty::Unknown.into()
                                            } else {
                                                sig
                                            }
                                        }
                                        hir::DefinitionStatus::UnknownFile => {
                                            unreachable!(
                                                "a module wasn't added: {:?}",
                                                file.debug(self.interner)
                                            )
                                        }
                                        hir::DefinitionStatus::UnknownDefinition => {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::UnknownFqn { fqn: fn_loc },
                                                file: self.loc.file(),
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
                                                        file: self.loc.file(),
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
                                                    file: self.loc.file(),
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
                        Expr::Call { callee, args } => 'call: {
                            let mut callee_ty = self.tys[self.loc][*callee];

                            // This is the second stage of handling generic function calls.
                            // After the generic function has been fully resolved with its
                            // generic arguments we need to fetch the new signature
                            if let Ty::NaivePolymorphicFunction { fn_loc } = callee_ty.absolute_ty()
                                && let Some(comptime_args) =
                                    self.call_associated_generics.get(&(self.loc, expr))
                            {
                                debug!(
                                    "STAGE 2 : {}\n        : {}\n        : #{}",
                                    match fn_loc {
                                        NaiveLoc::Global(_) => "global",
                                        NaiveLoc::Lambda(_) => "lambda",
                                    },
                                    fn_loc.debug(self.interner),
                                    callee.into_raw()
                                );

                                let actual_fn_loc = fn_loc.make_concrete(Some(*comptime_args));

                                debug!("sig of {}", actual_fn_loc.debug(self.interner));
                                let sig = self.tys.sig(actual_fn_loc);
                                debug!("     = {}", sig.debug(self.interner, true));

                                callee_ty = sig;

                                // todo: is replacing the weak types good?
                                // What if a generic function is alaised?
                                self.replace_weak_tys(*callee, sig);
                            }

                            match callee_ty.absolute_ty() {
                                // This is the first stage of handling generic function calls.
                                // It evaluates all the comptime arguments,
                                // and then returns with an error which will force the generic
                                // function to be reevaluated with these new comptime arguments
                                Ty::NaivePolymorphicFunction { fn_loc } => {
                                    debug!(
                                        "STAGE 1 : {}\n        : {}\n        : #{}",
                                        match fn_loc {
                                            NaiveLoc::Global(_) => "global",
                                            NaiveLoc::Lambda(_) => "lambda",
                                        },
                                        fn_loc.debug(self.interner),
                                        callee.into_raw()
                                    );

                                    assert_eq!(
                                        self.tys.try_naive(*fn_loc, self.world_bodies),
                                        Err(NaiveLookupErr::IsPolymorphic)
                                    );

                                    let generic_body = match fn_loc {
                                        NaiveLoc::Global(global) => self.world_bodies
                                            [fn_loc.file()]
                                        .global_body(global.name()),
                                        NaiveLoc::Lambda(lambda) => lambda.expr(),
                                    };

                                    let Expr::Lambda(lambda) =
                                        self.world_bodies[fn_loc.file()][generic_body]
                                    else {
                                        todo!("figure out what to do when this happens")
                                    };

                                    for arg in args {
                                        // done beforehand so that errors don't get reported twice
                                        self.is_safe_to_compile(self.loc, *arg)?;
                                    }

                                    let comptime_args = match self.evaluate_comptime_args(
                                        NaiveLambdaLoc {
                                            file: fn_loc.file(),
                                            expr: generic_body,
                                            lambda,
                                        },
                                        args,
                                        expr,
                                    ) {
                                        Ok(Ok(comptime_args)) => comptime_args,
                                        Ok(Err(ArgsContainDiagnostics)) => {
                                            debug!(
                                                "clearing inline on args contain diagnostics error"
                                            );
                                            self.inline_comptime_args.clear();
                                            self.inline_comptime_tys.clear();
                                            break 'call Ty::Unknown.into();
                                        }
                                        Err(why) => {
                                            debug!("clearing inline on InferResult Err");
                                            // TODO: I don't think this should be done.
                                            // The inline info should be saved so that it can
                                            // be used on the next run.
                                            self.inline_comptime_args.clear();
                                            self.inline_comptime_tys.clear();
                                            return Err(why);
                                        }
                                    };

                                    if let NaiveLoc::Lambda(lambda_loc) = fn_loc {
                                        let lambda_headers = self
                                            .infer_lambda_headers(
                                                generic_body,
                                                lambda,
                                                Some(comptime_args),
                                                false,
                                            )?
                                            .expect("comptime arguments were already passed");

                                        let lambda_loc =
                                            lambda_loc.make_concrete(Some(comptime_args));

                                        let hir::Lambda {
                                            params: param_exprs,
                                            return_ty: return_ty_expr,
                                            ..
                                        } = &self.bodies[lambda];

                                        self.init_new_concrete(
                                            lambda_loc,
                                            param_exprs,
                                            return_ty_expr,
                                            lambda_headers.param_tys,
                                            lambda_headers.return_ty,
                                        );
                                    } else {
                                        assert!(
                                            comptime_args
                                                .into_value_range()
                                                .eq(self.inline_comptime_args.iter().copied()),
                                            "self.comptime_args was unexpectedly updated during `infer_lambda_headers`",
                                        );
                                        assert_eq!(
                                            comptime_args.into_value_range().len(),
                                            self.inline_comptime_tys.len(),
                                            "self.comptime_tys was unexpectedly updated during `infer_lambda_headers`",
                                        );

                                        self.inline_comptime_args.clear();
                                        self.inline_comptime_tys.clear();
                                        debug!("  clear inline info");
                                    }

                                    self.call_associated_generics
                                        .insert((self.loc, expr), comptime_args);

                                    let specialized_loc = fn_loc.make_concrete(Some(comptime_args));

                                    debug!(
                                        "generic call submit {}",
                                        specialized_loc.debug(self.interner)
                                    );

                                    // this will cause the function to be reevaluated
                                    // its brand new compile-time arguments.
                                    //
                                    // This call expression will also then be reevaluated,
                                    // and the "second stage" listed above will activate
                                    return Err(vec![specialized_loc]);
                                }
                                Ty::ConcreteFunction {
                                    param_tys,
                                    return_ty,
                                    ..
                                }
                                | Ty::FunctionPointer {
                                    param_tys,
                                    return_ty,
                                } => {
                                    let mut params_iter = param_tys.iter();
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
                                                            expected: ExpectedTy::Concrete(
                                                                param_ty,
                                                            ),
                                                        },
                                                        file: self.loc.file(),
                                                        expr: Some(expr),
                                                        range: TextRange::empty(call_end),
                                                        help: None,
                                                    });
                                                }
                                            } else {
                                                break;
                                            }
                                            current_param = params_iter.next();
                                            continue;
                                        };
                                        let arg_ty = self.tys[self.loc][*arg];

                                        let Some(param) = current_param else {
                                            // there are more args than params
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::ExtraArg { found: arg_ty },
                                                file: self.loc.file(),
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
                                                        expected: ExpectedTy::Concrete(
                                                            actual_sub_ty,
                                                        ),
                                                        found: arg_ty,
                                                    },
                                                    file: self.loc.file(),
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

                                    *return_ty
                                }
                                _ => {
                                    if *callee_ty != Ty::Unknown {
                                        debug!(
                                            "{} #{} is not a function ({})",
                                            self.loc.debug(self.interner),
                                            callee.into_raw(),
                                            callee_ty.debug(self.interner, true)
                                        );
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::CalledNonFunction {
                                                found: callee_ty,
                                            },
                                            file: self.loc.file(),
                                            expr: Some(expr),
                                            range: self.bodies.range_for_expr(expr),
                                            help: None,
                                        });
                                    }

                                    Ty::Unknown.into()
                                }
                            }
                        }
                        // Type inference for lambda expressions.
                        //
                        // Typically how these are handled is that the Expr::Lambda
                        // (the headers) are type-checked in the current scope.
                        //
                        // The body of the lambda itself is not type-checked here
                        // or in this scope.
                        //
                        // The block which is the body of the lambda will be type-checked
                        // with its own GlobalInferenceCtx.
                        //
                        // The type-checking of the lambda will submit its own
                        // body to be type-checked if it is either
                        // a) not polymorphic, or
                        // b) polymorphic, but `self.loc` refers to this lambda
                        //    and contains the comptime arguments
                        //
                        // A polymorphic function that never gets called will
                        // never has its body type-checked.
                        // TODO: maybe change that
                        Expr::Lambda(lambda) => 'lambda: {
                            let hir::Lambda {
                                params,
                                return_ty: return_ty_expr,
                                ..
                            } = &self.bodies[*lambda];

                            let lambda_loc = NaiveLambdaLoc {
                                file: self.loc.file(),
                                expr,
                                lambda: *lambda,
                            };

                            // if the lambda is directly attached to a global,
                            // then associate the lambda with that global name

                            let self_loc_expr = match self.loc {
                                ConcreteLoc::Global(global) => {
                                    self.world_bodies.global_body(global.to_naive())
                                }
                                ConcreteLoc::Lambda(lambda) => lambda.expr(),
                            };
                            // "is the entire GlobalInferenceCtx dedicated to this lambda"
                            let this_is_special = expr == self_loc_expr;

                            if this_is_special && let ConcreteLoc::Global(global) = self.loc {
                                set_lambda_global(lambda_loc, global.to_naive());
                            }

                            assert!(self.inline_comptime_tys.is_empty());
                            assert!(self.inline_comptime_args.is_empty());

                            let loc_expr = match self.loc {
                                ConcreteLoc::Global(global) => {
                                    self.world_bodies.global_body(global.to_naive())
                                }
                                ConcreteLoc::Lambda(lambda) => lambda.expr(),
                            };
                            // "is the entire GlobalInferenceCtx dedicated to this lambda"
                            let this_is_special = expr == loc_expr;

                            debug!(
                                "inferring = {}\n self.loc = #{}\n   lambda = #{}\n  special = {}",
                                self.loc.debug(self.interner),
                                loc_expr.into_raw(),
                                expr.into_raw(),
                                this_is_special,
                            );

                            let comptime_args = if this_is_special {
                                self.loc.comptime_args()
                            } else {
                                None
                            };

                            debug!("{comptime_args:?}");

                            assert!(self.inline_comptime_args.is_empty());
                            assert!(self.inline_comptime_tys.is_empty());

                            self.inline_comptime_args
                                .extend(comptime_args.iter().flat_map(|c| c.into_value_range()));

                            // try to type the headers of the lambda
                            let lambda_headers = match self.infer_lambda_headers(
                                expr,
                                *lambda,
                                comptime_args,
                                true,
                            )? {
                                Ok(typed) => typed,
                                Err(RequiresComptimeArgs) => {
                                    debug!("giving up");
                                    break 'lambda Ty::NaivePolymorphicFunction {
                                        // TODO: use the global_loc if its available
                                        fn_loc: lambda_loc.wrap(),
                                    }
                                    .into();
                                }
                            };

                            // todo: what if one lambda does an inline access WITHIN
                            // the headers of a second lambda which also has inline accesses

                            // This takes in a newly minted ConcreteLambdaLoc,
                            // and will do the needed initialization so it can
                            // be used as a new type location

                            if !lambda_headers.any_comptime {
                                // this is a regular function (not polymorphic)

                                // debug!("   non-polymorphic");
                                // debug!("   @{}", self.loc.debug(self.interner));

                                if lambda_headers.is_type {
                                    // debug!("  metaty insert #{expr:?} <- function pointer");
                                    self.tys[self.loc].meta_tys.insert(
                                        expr,
                                        Ty::FunctionPointer {
                                            param_tys: lambda_headers.param_tys,
                                            return_ty: lambda_headers.return_ty,
                                        }
                                        .into(),
                                    );
                                    break 'lambda Ty::Type.into();
                                }

                                // this is not a polymorphic function.
                                let lambda_loc = lambda_loc.make_concrete(None);

                                self.init_new_concrete(
                                    lambda_loc,
                                    params,
                                    return_ty_expr,
                                    lambda_headers.param_tys,
                                    lambda_headers.return_ty,
                                );

                                return Err(vec![lambda_loc.wrap()]);
                            } else {
                                // this is a polymorphic function

                                // debug!("   polymorphic");
                                // debug!("   @{}", self.loc.debug(self.interner));

                                if lambda_headers.is_type {
                                    // generic function types cannot be first-class,
                                    // that doesn't make sense with how the syntax works.
                                    self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::FunctionTypeWithComptimeParameters,
                                        file: self.loc.file(),
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });

                                    break 'lambda Ty::Unknown.into();
                                } else if this_is_special {
                                    // if this particular lambda header is the star of the show
                                    // (we're the location being resolved),
                                    // AND we were supplied with compile-time arguments,
                                    // then we can resolve ourselves using those compile-time arguments
                                    //
                                    // otherwise, we couldn't evaluate this polymorphic lambda
                                    // because we wouldn't have enough information.

                                    let lambda_loc =
                                        lambda_loc.make_concrete(self.loc.comptime_args());

                                    self.init_new_concrete(
                                        lambda_loc,
                                        params,
                                        return_ty_expr,
                                        lambda_headers.param_tys,
                                        lambda_headers.return_ty,
                                    );

                                    return Err(vec![lambda_loc.wrap()]);
                                } else {
                                    // we're just some rando third-wheel generic lambda with no
                                    // idea what to use for our signature

                                    // println!("   unresolved polymorphic");

                                    break 'lambda Ty::NaivePolymorphicFunction {
                                        fn_loc: lambda_loc.wrap(),
                                    }
                                    .into();
                                }
                            }
                        }
                        Expr::Comptime(comptime) => {
                            let hir::Comptime { body } = self.bodies[*comptime];

                            let ty = self.tys[self.loc][body];

                            if ty.is_pointer() || ty.is_function() {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::ComptimePointer,
                                    file: self.loc.file(),
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
                                        (name.name, (name.range, value, self.tys[self.loc][value]))
                                    })
                                })
                                .collect::<IndexMap<_, _>>();

                            let expected_tys = match expected_ty.as_struct() {
                                Some(f) => f,
                                None => {
                                    self.tys[self.loc].expr_tys.insert(expr, Ty::Unknown.into());

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
                                        file: self.loc.file(),
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
                                        file: self.loc.file(),
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
                                        ty: self.tys[self.loc][value],
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
                            let inner_ty = self.tys[self.loc][*inner];

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
                                    file: self.loc.file(),
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
                                            file: self.loc.file(),
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };
                                    let sum_ty = self.tys[self.loc][*vary_val];
                                    if !self.expect_match(sum_ty, ExpectedTy::SumType, *vary_val) {
                                        break 'blk Ty::Unknown.into();
                                    }

                                    // second arg = variant type
                                    if let Some(variant_ty_val) = args.next() {
                                        let variant_ty = self.tys[self.loc][*variant_ty_val];
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
                                                file: self.loc.file(),
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
                                                    found: self.tys[self.loc][*arg],
                                                },
                                                file: self.loc.file(),
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
                                            file: self.loc.file(),
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
                                            file: self.loc.file(),
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };
                                    let sum_ty = self.tys[self.loc][*vary_val];
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
                                            file: self.loc.file(),
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };

                                    let variant_ty = self.tys[self.loc][*variant_ty_val];
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
                                            file: self.loc.file(),
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
                                                found: self.tys[self.loc][*arg],
                                            },
                                            file: self.loc.file(),
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
                                            file: self.loc.file(),
                                            expr: Some(expr),
                                            range: call_end,
                                            help: None,
                                        });
                                        break 'blk Ty::Unknown.into();
                                    };
                                    let name_ty = self.tys[self.loc][*name_val];
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
                                            file: self.loc.file(),
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
                                            file: self.loc.file(),
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
                                        file: self.loc.file(),
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

                    self.tys[self.loc].expr_tys.insert(expr, ty);
                }
                Descendant::PostExpr(_) => unreachable!(),
                Descendant::PreStmt(stmt) => {
                    if self.inferred_stmts.contains(&(self.loc, stmt)) {
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

                                debug!(
                                    "l{:?} : {}",
                                    local_def.into_raw(),
                                    ty_annotation.debug(self.interner, true)
                                );

                                // the definition has an annotation, so the value should match
                                if let Some(value) = def_body.value {
                                    // note: type annotations get inserted into `expected_tys`
                                    // in a different loop at the beginning of the `infer_expr`
                                    // function

                                    let value_ty = self.tys[self.loc][value];
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
                                        file: self.loc.file(),
                                        expr: Some(ty_annotation_expr),
                                        range: self.bodies.range_for_expr(ty_annotation_expr),
                                        help: None,
                                    });
                                }

                                self.tys[self.loc]
                                    .local_tys
                                    .insert(local_def, ty_annotation);
                            } else {
                                // the definition does not have an annotation,
                                // so use the type of it's value
                                let value_ty = def_body
                                    .value
                                    .map(|value| self.tys[self.loc][value])
                                    .unwrap_or(Ty::Unknown.into());
                                self.tys[self.loc].local_tys.insert(local_def, value_ty);
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
                                    file: self.loc.file(),
                                    // making expr the dest isn't technically correct, but it works
                                    expr: Some(assign_body.dest),
                                    range: assign_body.range,
                                    help: non_mut_help,
                                });
                                continue;
                            }

                            let dest_ty = self.tys[self.loc][assign_body.dest];
                            let value_ty = self.tys[self.loc][assign_body.value];

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
                                            file: self.loc.file(),
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
                                        file: self.loc.file(),
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
                            let value_ty = value
                                .map_or_else(|| Ty::Void.into(), |value| self.tys[self.loc][value]);

                            let range =
                                value.map_or(range, |value| self.bodies.range_for_expr(value));

                            self.break_with(label, value, range, value_ty, true);
                        }
                        Stmt::Continue { .. } => {}
                        Stmt::Defer { expr, .. } => {
                            self.find_usages(&[expr], stmt);
                        }
                    }

                    self.inferred_stmts.insert((self.loc, stmt));
                }
                // Although the type is called *PostStmt*, since we reversed the list these
                // actually come *before* all their inner subexpressions.
                //
                // This is useful because inserting a value into `expected_tys` will change
                // how types get resolved and how errors get reported
                Descendant::PostStmt(stmt) => {
                    if self.inferred_stmts.contains(&(self.loc, stmt)) {
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

        Ok(self.tys[self.loc][expr])
    }

    /// This will clear `inline_comptime_args` and `inline_comptime_tys`
    fn infer_lambda_headers(
        &mut self,
        expr: Idx<Expr>,
        lambda: Idx<hir::Lambda>,
        // this isn't actually used, `infer_lambda_headers` just ensures
        // that it matches with the value in `self.inline_comptime_args`
        comptime_args: Option<ComptimeArgs>,
        // If you already called `evaluate_comptime_args`, set this to false.
        // If you were only given `comptime_args`, then set this to true.
        add_comptime_tys: bool,
    ) -> InferResult<Result<TypedLambdaHeaders, RequiresComptimeArgs>> {
        let hir::Lambda {
            params,
            return_ty: return_ty_expr,
            body,
            ..
        } = &self.bodies[lambda];

        let comptime_args_len = comptime_args.map_or(0, |args| args.into_value_range().len());

        debug!("add_comptime_tys = {add_comptime_tys}");
        debug!("comptime_args_len = {comptime_args_len}");

        assert!(
            comptime_args
                .iter()
                .flat_map(|c| c.into_value_range())
                .eq(self.inline_comptime_args.iter().copied()),
            "infer_lambda_headers was passed comptime args ({}), but these don't match self.inline_comptime_args ({})",
            comptime_args_len,
            self.inline_comptime_args.len()
        );
        if add_comptime_tys {
            assert!(
                self.inline_comptime_tys.is_empty(),
                "infer_lambda_headers was told to handle inline comptime types itself, but self.inline_comptime_tys isn't empty ({})",
                self.inline_comptime_tys.len()
            );
        } else {
            assert_eq!(
                comptime_args_len,
                self.inline_comptime_tys.len(),
                "infer_lambda_headers was passed comptime args ({}), but these don't match self.inline_comptime_tys ({})",
                comptime_args_len,
                self.inline_comptime_tys.len()
            );
        }

        let is_type = *body == hir::LambdaBody::Empty && return_ty_expr.is_some();

        // we first check for comptime + inline parameter references
        let any_inline_param_refs = params
            .iter()
            .map(|p| p.ty)
            .chain(return_ty_expr.iter().copied())
            .flat_map(|expr| {
                self.bodies
                    .descendants(
                        expr,
                        hir::DescentOpts::All {
                            include_lambdas: false,
                            include_post_exprs: false,
                            include_post_stmts: false,
                        },
                    )
                    .filter_map(|d| match d {
                        Descendant::PreExpr(idx) => Some(idx),
                        Descendant::PostExpr(_) => unreachable!(),
                        Descendant::PreStmt(_) => None,
                        Descendant::PostStmt(_) => unreachable!(),
                    })
            })
            .any(|expr| matches!(self.bodies[expr], Expr::InlineParam { .. }));

        if any_inline_param_refs && self.inline_comptime_args.is_empty() {
            return Ok(Err(RequiresComptimeArgs));
        }

        let mut param_tys = Vec::with_capacity(params.len());

        let mut comptime_idx = 0;

        for (idx, param) in params.iter().enumerate() {
            // debug!("param p{idx}");

            let mut ty = self.const_ty(param.ty)?;

            if add_comptime_tys && any_inline_param_refs && param.comptime {
                self.inline_comptime_tys.push(ty);
                debug!("  push inline type {}", ty.debug(self.interner, true));
            }

            let mut impossible_to_differentiate = false;

            if let Some(last_param) = idx
                .checked_sub(1)
                .and_then(|idx| params.get(idx))
                .filter(|p| p.varargs)
            {
                // we already called `const_ty` on the last param
                let last_ty = self.tys[self.loc].meta_tys[last_param.ty];

                if !ty.can_differentiate_from(&last_ty) {
                    impossible_to_differentiate = true;
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::ImpossibleToDifferentiateVarArgs {
                            previous_ty: last_ty,
                            current_ty: ty,
                        },
                        file: self.loc.file(),
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
                        file: self.loc.file(),
                        expr: Some(expr),
                        range: param.range,
                        help: None,
                    });
                }
            }

            param_tys.push(ParamTy {
                ty,
                comptime: if param.comptime {
                    comptime_idx += 1;

                    Some(comptime_idx - 1)
                } else {
                    None
                },
                varargs: param.varargs,
                impossible_to_differentiate,
            });
        }

        let return_ty = if let Some(return_ty) = return_ty_expr {
            self.const_ty(*return_ty)?
        } else {
            Ty::Void.into()
        };

        // assert a second time, to ensure the lists weren't changed or updated
        assert!(
            comptime_args
                .iter()
                .flat_map(|c| c.into_value_range())
                .eq(self.inline_comptime_args.iter().copied()),
            "self.comptime_args was unexpectedly updated during `infer_lambda_headers`",
        );
        if any_inline_param_refs {
            assert_eq!(
                comptime_args_len,
                self.inline_comptime_tys.len(),
                "self.comptime_tys was unexpectedly updated during `infer_lambda_headers`",
            );
        }

        self.inline_comptime_tys.clear();
        self.inline_comptime_args.clear();
        debug!("  clear inline info");

        Ok(Ok(TypedLambdaHeaders {
            param_tys,
            return_ty,
            any_comptime: comptime_idx > 0,
            is_type,
        }))
    }

    /// This will add values to `inline_comptime_tys` and `inline_comptime_args`
    ///
    /// It is your responsibility to clear these lists
    ///
    /// TODO: detect and prevent recursive generic function calls
    fn evaluate_comptime_args(
        &mut self,
        lambda_loc: NaiveLambdaLoc,
        args: &[Idx<Expr>],
        call_expr: Idx<Expr>,
    ) -> InferResult<Result<ComptimeArgs, ArgsContainDiagnostics>> {
        let lambda_body = &self.world_bodies[lambda_loc.file()][lambda_loc.lambda()];

        let mut mismatch = false;

        assert!(self.inline_comptime_args.is_empty());
        if !self.inline_comptime_tys.is_empty() {
            debug!("self.inline_comptime_tys = {:?}", self.inline_comptime_tys);
        }
        assert!(self.inline_comptime_tys.is_empty());

        let dummy_loc = lambda_loc.make_concrete(None).wrap();

        if lambda_loc.file() != self.loc.file() {
            self.tys.create_area_if_not_exists(dummy_loc);
        }

        let call_range = self.bodies.range_for_expr(call_expr);
        let call_end = call_range
            .end()
            .checked_sub(TextSize::new(1))
            .unwrap_or(call_range.end());

        let mut comptime_idx = 0;
        for (idx, param) in lambda_body.params.iter().enumerate() {
            // todo: can the param.name.is_some() screw things up in regards to
            // inline_comptime_tys and inline_comptime_args
            if param.comptime && param.name.is_some() {
                // Parameters cannot reference themselves,
                // inline parameter references are always earlier comptime
                // parameters. For this reason, this should be safe
                // TODO: assert that
                let param_ty = if lambda_loc.file() != self.loc.file() {
                    let mut dummy_env = GlobalInferenceCtx {
                        loc: dummy_loc,
                        world_index: self.world_index,
                        world_bodies: self.world_bodies,
                        bodies: &self.world_bodies[lambda_loc.file()],
                        interner: self.interner,
                        expected_tys: Default::default(),
                        local_usages: Default::default(),
                        generics_arena: self.generics_arena,
                        call_associated_generics: self.call_associated_generics,
                        inferred_stmts: self.inferred_stmts,
                        tys: self.tys,
                        param_tys: Default::default(),
                        inline_comptime_args: Default::default(),
                        inline_comptime_tys: self.inline_comptime_tys.clone(),
                        all_finished_locations: self.all_finished_locations,
                        to_infer: self.to_infer,
                        diagnostics: self.diagnostics,
                        eval_comptime: self.eval_comptime,
                    };

                    // TODO: handle the error properly, and test the error case
                    dummy_env.const_ty(param.ty).unwrap()
                } else {
                    self.const_ty(param.ty)?
                };

                self.inline_comptime_tys.push(param_ty);
                debug!("  push inline type {}", param_ty.debug(self.interner, true));

                let Some(arg) = args.get(idx) else {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::MissingArg {
                            expected: ExpectedTy::Concrete(param_ty),
                        },
                        file: self.loc.file(),
                        expr: Some(call_expr),
                        range: TextRange::empty(call_end),
                        help: None,
                    });
                    return Ok(Err(ArgsContainDiagnostics));
                };

                let arg_ty = self.tys[self.loc][*arg];

                // if expect match throws an error, none of the other param types
                // will be calculated and only the other comptime args will
                // throw errors. idk if that's a good thing.
                if !self.expect_match(arg_ty, ExpectedTy::Concrete(param_ty), *arg) {
                    mismatch = true;
                    continue;
                }

                let arg_const = self.get_const(*arg);
                if !arg_const.is_const() {
                    if arg_const.should_report_not_const() {
                        self.diagnostics.push(TyDiagnostic {
                            kind: TyDiagnosticKind::ComptimeArgNotConst {
                                param_name: param.name.unwrap().0,
                                param_ty,
                            },
                            file: self.loc.file(),
                            range: self.bodies.range_for_expr(*arg),
                            expr: Some(*arg),
                            help: None,
                        });
                    }
                    return Ok(Err(ArgsContainDiagnostics));
                }

                let res = self
                    .const_data(self.loc, *arg)
                    // the only reason const_data would return an Err
                    // is because of is_safe_to_compile, but we already called
                    // all of them.
                    .expect("is_safe_to_compile was done beforehand")
                    .unwrap_or_else(|| {
                        panic!(
                            "@{} expr #{} didn't work",
                            self.loc.debug(self.interner),
                            arg.into_raw()
                        )
                    });
                let res = self.generics_arena.alloc(res);

                self.inline_comptime_args.push(res);

                assert_eq!(self.inline_comptime_args.len(), comptime_idx + 1);
                comptime_idx += 1;
            }
        }

        if lambda_loc.file() != self.loc.file() {
            self.tys.remove_area(dummy_loc);
        }

        if mismatch {
            return Ok(Err(ArgsContainDiagnostics));
        }

        // ensures that nothing else was allocated while the args were being allocated
        for pair in self.inline_comptime_args.windows(2) {
            let [prev, next] = pair else { unreachable!() };

            assert!(prev.into_raw().into_u32() + 1 == next.into_raw().into_u32());
        }

        let range = if let Some(first) = self.inline_comptime_args.first() {
            let last = self.inline_comptime_args.last().unwrap();

            IdxRange::new_inclusive((*first)..=(*last))
        } else {
            // this is just to get an empty list
            self.generics_arena.alloc_many([])
        };

        let comptime_args = ComptimeArgs::new(range);

        Ok(Ok(comptime_args))
    }

    /// Type information is duplicated between the area in which the lambda header resides,
    /// and the area in which the lambda body resides.
    ///
    /// This function does that copying
    fn init_new_concrete(
        &mut self,
        lambda_loc: ConcreteLambdaLoc,
        param_exprs: &Vec<hir::Param>,
        ret_ty_expr: &Option<Idx<Expr>>,
        param_tys: Vec<ParamTy>,
        return_ty: Intern<Ty>,
    ) {
        // // set the body of the lambda ready to be processed
        // // with those comptime args
        // self.to_infer.insert(lambda_loc);

        let lambda_ty: Intern<Ty> = Ty::ConcreteFunction {
            param_tys,
            return_ty,
            fn_loc: lambda_loc,
        }
        .into();

        // The type of the lambda headers will appear in both
        // the concrete location that contained the lambda,
        // and the body of the lambda itself.
        //
        // e.g.
        // ```
        // foo :: () -> u32 {
        //   42
        // }
        // ```
        //
        // will produce:
        // ```
        // main::foo
        // - #2 () -> u32
        //
        // main::lambda#0
        // - #0 {uint}
        // - #1 {uint}
        // - #2 () -> u32
        // ```
        if self.loc != lambda_loc.wrap() {
            debug!(
                "copying the concrete function type `{}` at #{} from {} -> {}",
                lambda_ty.debug(self.interner, true),
                lambda_loc.expr().into_raw(),
                self.loc.debug(self.interner),
                lambda_loc.debug(self.interner)
            );
            self.tys
                .create_area_if_not_exists(lambda_loc.wrap())
                .expr_tys
                .insert(lambda_loc.expr(), lambda_ty);

            // the meta types have to be copied over.
            // these store the meta type value of each parameter.
            // e.g. for (x: i32, y: bool) -> void,
            // the meta type "i32" will be copied to the new location
            // of the type annotation,
            // and the same for "bool"
            let exprs_to_copy = param_exprs
                .iter()
                .map(|p| p.ty)
                .chain(ret_ty_expr.iter().copied())
                .flat_map(|expr| {
                    self.bodies
                        .descendants(
                            expr,
                            hir::DescentOpts::All {
                                include_lambdas: false,
                                include_post_exprs: false,
                                include_post_stmts: false,
                            },
                        )
                        .filter_map(|d| match d {
                            Descendant::PreExpr(idx) => Some(idx),
                            Descendant::PostExpr(_) => unreachable!(),
                            Descendant::PreStmt(_) => None,
                            Descendant::PostStmt(_) => unreachable!(),
                        })
                });

            // see earlier
            for to_copy in exprs_to_copy {
                if let Some(ty) = self.tys[self.loc].try_get_expr(to_copy) {
                    debug!(
                        "  copying the expr type `{}` at #{} from {} -> {}",
                        ty.debug(self.interner, true),
                        to_copy.into_raw(),
                        self.loc.debug(self.interner),
                        lambda_loc.debug(self.interner)
                    );

                    self.tys[lambda_loc.wrap()].expr_tys.insert(to_copy, ty);
                }

                if let Some(ty) = self.tys[self.loc].meta_ty(to_copy) {
                    debug!(
                        "  copying the meta type `{}` at #{} from {} -> {}",
                        ty.debug(self.interner, true),
                        to_copy.into_raw(),
                        self.loc.debug(self.interner),
                        lambda_loc.debug(self.interner)
                    );

                    self.tys[lambda_loc.wrap()].meta_tys.insert(to_copy, ty);
                }
            }
        }

        self.tys[self.loc]
            .expr_tys
            .insert(lambda_loc.expr(), lambda_ty);
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
                        file: self.loc.file(),
                        expr: value,
                        range: self.bodies.range_for_expr(value.unwrap()),
                        help: None,
                    });

                    self.tys[self.loc]
                        .expr_tys
                        .insert(referenced_expr, Ty::Unknown.into());
                } else {
                    // the type just hasn't been set yet
                    self.tys[self.loc].expr_tys.insert(referenced_expr, ty);
                }
            }
        }
    }

    fn try_get_previous_ty(&self, expr: Idx<Expr>) -> Option<Intern<Ty>> {
        self.tys[self.loc]
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
            self.tys[self.loc].expr_tys.insert(block_expr, max);
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
                file: self.loc.file(),
                expr: Some(found_expr.unwrap_or(block_expr)),
                range: found_range,
                help: Some(help),
            });

            // make the block type unknown so errors don't get reported twice in a row
            self.tys[self.loc]
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
                file: self.loc.file(),
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
                file: self.loc.file(),
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

            self.tys[self.loc].expr_tys[expr] = expected;

            if let Some(max_size) = expected.get_max_int_size() {
                if *num > max_size {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::IntTooBigForType {
                            found: *num,
                            max: max_size,
                            ty: expected,
                        },
                        file: self.loc.file(),
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
                    found.debug(self.interner, true),
                    expected_ty.debug(self.interner, true),
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
                file: self.loc.file(),
                expr: Some(expr),
                range: self.bodies.range_for_expr(expr),
                help,
            });

            false
        }
    }

    fn naive_global_to_ty(
        &mut self,
        naive: NaiveGlobalLoc,
        file_expr: Option<Idx<hir::Expr>>,
        total_expr: Idx<hir::Expr>,
        name_range: TextRange,
    ) -> InferResult<Intern<Ty>> {
        // println!("naive_location_to_ty {}", naive.debug(self.interner));

        match self.world_index.definition(naive) {
            hir::DefinitionStatus::Defined => {
                // println!("defined {}", naive.debug(self.interner));

                // this should also set the meta type
                let ty = match self.tys.try_naive(naive.wrap(), self.world_bodies) {
                    Ok(sig) => sig,
                    Err(NaiveLookupErr::IsPolymorphic) => todo!(),
                    Err(NaiveLookupErr::NotFound) => {
                        // println!(" - not found");
                        assert!(!self.world_bodies.has_polymorphic_body(naive.wrap()));
                        let tfqn = naive.make_concrete(None);
                        return Err(vec![tfqn.wrap()]);
                    }
                };

                // println!(" - found");

                let tfqn = naive.make_concrete(None);

                if *ty == Ty::Unknown {
                    return Ok(Ty::Unknown.into());
                }

                if *ty == Ty::NotYetResolved {
                    self.diagnostics.push(TyDiagnostic {
                        kind: TyDiagnosticKind::NotYetResolved { fqn: naive },
                        file: self.loc.file(),
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
                            file: self.loc.file(),
                            expr: Some(total_expr),
                            range: name_range,
                            help: None,
                        });
                    }
                    return Ok(Ty::Unknown.into());
                }

                let global_body = self.world_bodies.global_body(naive);

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
                let old_tfqn = std::mem::replace(&mut self.loc, tfqn.wrap());
                let actual_ty = self.const_ty(global_body)?;
                self.loc = old_tfqn;

                if actual_ty.can_have_a_name() {
                    set_type_name(actual_ty, TyName::Global(tfqn));
                }

                Ok(actual_ty)
            }
            hir::DefinitionStatus::UnknownFile => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFile { file: naive.file() },
                    file: self.loc.file(),
                    expr: file_expr,
                    range: self.bodies.range_for_expr(file_expr.unwrap()),
                    help: None,
                });
                Ok(Ty::Unknown.into())
            }
            hir::DefinitionStatus::UnknownDefinition => {
                self.diagnostics.push(TyDiagnostic {
                    kind: TyDiagnosticKind::UnknownFqn { fqn: naive },
                    file: self.loc.file(),
                    expr: file_expr,
                    range: self.bodies.range_for_expr(file_expr.unwrap()),
                    help: None,
                });
                Ok(Ty::Unknown.into())
            }
        }
    }

    // todo! get rid of this somehow and just have const_data
    pub(crate) fn const_ty(&mut self, expr: Idx<hir::Expr>) -> InferResult<Intern<Ty>> {
        if let Some(meta_ty) = self.tys[self.loc].meta_ty(expr) {
            return Ok(meta_ty);
        }

        let include_local_value = |local| {
            let local_def = &self.bodies[local];
            let local_ty = self.tys[self.loc].local_tys[local];

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

        // let mut res = String::new();
        // hir::debug_descendants(
        //     &mut res,
        //     self.bodies,
        //     descendants.iter().rev().copied(),
        //     false,
        //     true,
        // );
        // debug!("CONST TYPE {}\n{res}", self.loc.debug(self.interner));

        for descendant in descendants.into_iter().rev() {
            match descendant {
                Descendant::PreExpr(expr) => {
                    if self.tys[self.loc].meta_ty(expr).is_some() {
                        continue;
                    }

                    let ty = match &self.bodies[expr] {
                        Expr::Missing => Ty::Unknown.into(),
                        Expr::Ref { mutable, expr } => {
                            let sub_ty = self.tys[self.loc].meta_ty(*expr).unwrap();

                            Ty::Pointer {
                                mutable: *mutable,
                                sub_ty,
                            }
                            .into()
                        }
                        Expr::Local(local_def) => 'branch: {
                            let local_ty = self.tys[self.loc].local_tys[*local_def];

                            if *local_ty == Ty::Unknown {
                                debug!("local unknown");
                                break 'branch Ty::Unknown.into();
                            }

                            if *local_ty != Ty::Type {
                                self.report_non_type(expr, local_ty);
                                println!("local not type");
                                break 'branch Ty::Unknown.into();
                            }

                            let local_def = &self.bodies[*local_def];

                            if local_def.mutable {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::LocalTyIsMutable,
                                    file: self.loc.file(),
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: Some(TyDiagnosticHelp {
                                        kind: TyDiagnosticHelpKind::MutableVariable,
                                        range: local_def.range,
                                    }),
                                });
                                println!("local mutable");

                                break 'branch Ty::Unknown.into();
                            }

                            // this protects against cases like `x ::;`
                            if let Some(value) = local_def.value {
                                let ty = self.tys[self.loc].meta_ty(value).unwrap();
                                debug!("  local get meta ty (#{value:?}) = {ty:?}");
                                ty
                            } else {
                                debug!("local has no value");
                                Ty::Unknown.into()
                            }
                        }
                        Expr::LocalGlobal(name) => self.naive_global_to_ty(
                            Fqn {
                                file: self.loc.file(),
                                name: name.name,
                            },
                            None,
                            expr,
                            name.range,
                        )?,
                        Expr::Param { idx, .. } => {
                            let param_ty = &self.param_tys[*idx as usize];
                            assert!(param_ty.comptime.is_none());

                            self.diagnostics.push(TyDiagnostic {
                                kind: TyDiagnosticKind::ParamNotATy,
                                file: self.loc.file(),
                                expr: Some(expr),
                                range: self.bodies.range_for_expr(expr),
                                help: None,
                            });

                            Ty::Unknown.into()
                        }
                        Expr::ComptimeParam {
                            real_idx,
                            comptime_idx,
                            ..
                        } => 'param: {
                            let param_ty = &self.param_tys[*real_idx as usize];
                            assert_eq!(param_ty.comptime, Some(*comptime_idx as usize));

                            if !self.expect_match(
                                param_ty.ty,
                                ExpectedTy::Concrete(Ty::Type.into()),
                                expr,
                            ) {
                                break 'param Ty::Unknown.into();
                            }

                            let comptime_result = self.loc
                                .comptime_args()
                                .expect("If we're referencing comptime args, we must be in a location that has comptime args")
                                .into_value_range()
                                .nth(*comptime_idx as usize)
                                .unwrap();

                            match self.generics_arena[comptime_result] {
                                ComptimeResult::Type(ty) => ty,
                                _ => unreachable!(),
                            }
                        }
                        Expr::InlineParam { comptime_idx, .. } => 'param: {
                            let param_ty = self.inline_comptime_tys[*comptime_idx as usize];

                            if !self.expect_match(
                                param_ty,
                                ExpectedTy::Concrete(Ty::Type.into()),
                                expr,
                            ) {
                                break 'param Ty::Unknown.into();
                            }

                            let comptime_result = self.inline_comptime_args[*comptime_idx as usize];

                            match self.generics_arena[comptime_result] {
                                ComptimeResult::Type(ty) => ty,
                                _ => unreachable!(),
                            }
                        }
                        Expr::Member { previous, name } => {
                            // todo: remove recursion

                            // this has to be done because `infer_fqn` will call
                            // `const_ty` on the type annotation of the fqn, even
                            // though it hasn't been processed by `infer_expr` yet
                            let previous_ty = self.infer_expr(*previous)?;

                            match previous_ty.as_ref() {
                                Ty::File(file) => self.naive_global_to_ty(
                                    Fqn {
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
                                    //     self.tys[self.loc].get_meta_ty(*previous).unwrap();
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
                                                    file: self.loc.file(),
                                                    expr: Some(expr),
                                                    range: self.bodies.range_for_expr(expr),
                                                    help: None,
                                                });

                                                Ty::Unknown.into()
                                            }),
                                        _ => {
                                            self.diagnostics.push(TyDiagnostic {
                                                kind: TyDiagnosticKind::CantUseAsTy,
                                                file: self.loc.file(),
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
                            let sub_ty = self.tys[self.loc].meta_tys[*ty];

                            if let Some(size) = size {
                                // we must infer it manually because it might not
                                // have been inferred.
                                let usize_ty = Ty::UInt(u8::MAX).into();
                                if !self.expect_match(
                                    self.tys[self.loc][*size],
                                    ExpectedTy::Concrete(usize_ty),
                                    *size,
                                ) {
                                    break 'branch Ty::Unknown.into();
                                }

                                self.replace_weak_tys(*size, usize_ty);

                                let expr_const = self.get_const(*size);
                                if !expr_const.is_const() {
                                    if expr_const.should_report_not_const() {
                                        self.diagnostics.push(TyDiagnostic {
                                            kind: TyDiagnosticKind::ArraySizeNotConst,
                                            file: self.loc.file(),
                                            range: self.bodies.range_for_expr(*size),
                                            expr: Some(*size),
                                            help: None,
                                        });
                                    }
                                    break 'branch Ty::Unknown.into();
                                }

                                debug!(
                                    "  starting to calc const_data of {size:?} at {:?}",
                                    self.loc.debug(self.interner)
                                );
                                match self.const_data(self.loc, *size)? {
                                    Some(ComptimeResult::Integer { num, .. }) => {
                                        Ty::ConcreteArray { size: num, sub_ty }.into()
                                    }
                                    actual_data => {
                                        panic!(
                                            "{} #{} already checked that the constant was an integer, and yet the data is {actual_data:?}",
                                            self.loc.debug(self.interner),
                                            expr.into_raw()
                                        );

                                        // // todo: we check that the array size is a `usize` above,
                                        // // soo... is this even reachable?
                                        // self.diagnostics.push(TyDiagnostic {
                                        //     kind: TyDiagnosticKind::ArraySizeNotInt,
                                        //     file: self.loc.file(),
                                        //     range: self.bodies.range_for_expr(*size),
                                        //     expr: Some(*size),
                                        //     help: None,
                                        // });

                                        // Ty::Unknown.into()
                                    }
                                }
                            } else {
                                Ty::Slice { sub_ty }.into()
                            }
                        }
                        Expr::Distinct { uid, ty } => Ty::Distinct {
                            uid: *uid,
                            sub_ty: self.tys[self.loc].meta_tys[*ty],
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
                                        ty: self.tys[self.loc].meta_tys[ty],
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
                                            self.tys[self.loc][discrim_expr],
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
                                                    file: self.loc.file(),
                                                    range: self.bodies.range_for_expr(discrim_expr),
                                                    expr: Some(discrim_expr),
                                                    help: None,
                                                });
                                            }
                                            break 'discrim_calc;
                                        }

                                        match self.const_data(self.loc, discrim_expr)? {
                                            Some(ComptimeResult::Integer { num, .. }) => {
                                                if used_discriminants.contains(&num) {
                                                    self.diagnostics.push(TyDiagnostic {
                                                        kind: TyDiagnosticKind::DiscriminantUsedAlready {
                                                            value: num
                                                        },
                                                        file: self.loc.file(),
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
                                            _ => unreachable!(),
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
                                    |ty| self.tys[self.loc].meta_tys[ty],
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

                            set_enum_uid(*enum_uid, enum_ty);

                            enum_ty
                        }
                        Expr::OptionalDecl { ty } => Ty::Optional {
                            sub_ty: self.tys[self.loc].meta_tys[*ty],
                        }
                        .into(),
                        Expr::ErrorUnionDecl {
                            error_ty,
                            payload_ty,
                        } => {
                            let error_ty = self.tys[self.loc].meta_tys[*error_ty];
                            let payload_ty = self.tys[self.loc].meta_tys[*payload_ty];

                            if !error_ty.can_differentiate_from(&payload_ty) {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::ImpossibleToDifferentiateErrorUnion {
                                        error_ty,
                                        payload_ty,
                                    },
                                    file: self.loc.file(),
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
                        Expr::Lambda(lambda) => 'lambda: {
                            let hir::Lambda { body, .. } = &self.bodies[*lambda];

                            let lambda_headers =
                                match self.infer_lambda_headers(expr, *lambda, None, false)? {
                                    Ok(headers) => headers,
                                    Err(RequiresComptimeArgs) => {
                                        self.diagnostics.push(TyDiagnostic {
                                        kind: TyDiagnosticKind::FunctionTypeWithComptimeParameters,
                                        file: self.loc.file(),
                                        expr: Some(expr),
                                        range: self.bodies.range_for_expr(expr),
                                        help: None,
                                    });
                                        break 'lambda Ty::Unknown.into();
                                    }
                                };

                            if lambda_headers.any_comptime {
                                self.diagnostics.push(TyDiagnostic {
                                    kind: TyDiagnosticKind::FunctionTypeWithComptimeParameters,
                                    file: self.loc.file(),
                                    expr: Some(expr),
                                    range: self.bodies.range_for_expr(expr),
                                    help: None,
                                });
                                break 'lambda Ty::Unknown.into();
                            }

                            // if the function has a body then it isn't a type
                            if *body != hir::LambdaBody::Empty {
                                let lambda_body_loc = NaiveLambdaLoc {
                                    file: self.loc.file(),
                                    expr,
                                    lambda: *lambda,
                                };

                                self.report_non_type(
                                    expr,
                                    Ty::ConcreteFunction {
                                        param_tys: lambda_headers.param_tys,
                                        return_ty: lambda_headers.return_ty,
                                        fn_loc: lambda_body_loc.make_concrete(None),
                                    }
                                    .into(),
                                );

                                break 'lambda Ty::Unknown.into();
                            }

                            Ty::FunctionPointer {
                                param_tys: lambda_headers.param_tys,
                                return_ty: lambda_headers.return_ty,
                            }
                            .into()
                        }
                        Expr::Comptime(comptime) => {
                            let hir::Comptime { body } = self.bodies[*comptime];

                            let ty = self.tys[self.loc][body];

                            if *ty == Ty::Type {
                                self.tys[self.loc].expr_tys.insert(expr, ty);

                                if self.is_safe_to_compile(self.loc, body)? {
                                    match (self.eval_comptime)(
                                        ComptimeLoc {
                                            loc: self.loc,
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
                            self.tys[self.loc].meta_ty(*paren_expr).unwrap()
                        }
                        _ => {
                            // TODO: remove recursion
                            let expr_ty = self.infer_expr(expr)?;

                            if expr_ty.is_zero_sized() {
                                debug!("{}", std::backtrace::Backtrace::force_capture());
                                debug!(
                                    "converting #{} ({:?}) into a const `{}` type",
                                    expr.into_raw(),
                                    self.bodies[expr],
                                    expr_ty.debug(self.interner, true),
                                );
                                expr_ty
                            } else {
                                self.report_non_type(expr, expr_ty);

                                Ty::Unknown.into()
                            }
                        }
                    };

                    // debug!(
                    //     "  metaty insert {} #{} <- {ty:?}",
                    //     self.loc.debug(self.interner),
                    //     expr.into_raw()
                    // );
                    self.tys[self.loc].meta_tys.insert(expr, ty);
                }
                Descendant::PostExpr(_) => unreachable!(),
                Descendant::PreStmt(_) => unreachable!(),
                Descendant::PostStmt(_) => unreachable!(),
            }
        }

        Ok(self.tys[self.loc].meta_tys[expr])
    }

    #[track_caller]
    pub(crate) fn const_data(
        &mut self,
        loc: ConcreteLoc,
        expr: Idx<hir::Expr>,
    ) -> InferResult<Option<ComptimeResult>> {
        // println!(
        //     "const_data @ {}, expr #{}",
        //     loc.debug(self.interner),
        //     expr.into_raw()
        // );

        if !self.tys[loc].expr_tys.contains_idx(expr) {
            panic!(
                "You should have inferred {} #{} before trying to call `const_data` on it",
                loc.debug(self.interner),
                expr.into_raw()
            );
        }

        match &self.world_bodies[loc.file()][expr] {
            Expr::IntLiteral(num) => Ok(Some(ComptimeResult::Integer {
                num: *num,
                bit_width: 32,
            })),
            Expr::FloatLiteral(num) => Ok(Some(ComptimeResult::Float {
                num: *num,
                bit_width: 32,
            })),
            Expr::Comptime(comptime) => {
                let hir::Comptime { body } = self.world_bodies[loc.file()][*comptime];

                if self.is_safe_to_compile(loc, body)? {
                    Ok(Some((self.eval_comptime)(
                        ComptimeLoc {
                            loc,
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
                let local_def = &self.world_bodies[loc.file()][*local_def];

                assert!(
                    local_def.value.is_some(),
                    "`get_const` should have set this type of variable to non-const"
                );

                // todo: remove recursion
                self.const_data(loc, local_def.value.unwrap())
            }
            Expr::LocalGlobal(global) => {
                let ufqn = Fqn {
                    file: loc.file(),
                    name: global.name,
                };

                assert!(!self.world_bodies.has_polymorphic_body(ufqn.wrap()));
                let tfqn = ufqn.make_concrete(None);

                // todo: remove recursion
                self.const_data(tfqn.wrap(), self.world_bodies.global_body(tfqn.to_naive()))
            }
            Expr::Member {
                previous,
                name: field,
            } => match self.tys[self.loc][*previous].as_ref() {
                Ty::File(file) => {
                    let ufqn = Fqn {
                        file: *file,
                        name: field.name,
                    };

                    assert!(!self.world_bodies.has_polymorphic_body(ufqn.wrap()));
                    let tfqn = ufqn.make_concrete(None);

                    // todo: remove recursion
                    self.const_data(tfqn.wrap(), self.world_bodies.global_body(tfqn.to_naive()))
                }
                _ => Ok(None),
            },
            Expr::ComptimeParam { comptime_idx, .. } => {
                let comptime_result = self.loc
                        .comptime_args()
                        .expect("If we're referencing comptime args, we must be in a location that has comptime args")
                        .into_value_range()
                        .nth(*comptime_idx as usize)
                        .unwrap();

                Ok(Some(self.generics_arena[comptime_result].clone()))
            }
            // todo: add the rest of the possible expressions in `is_const`
            _ => {
                if *self.tys[loc].expr_tys[expr] == Ty::Type
                    && let Some(meta_ty) = self.tys[loc].meta_ty(expr)
                {
                    Ok(Some(ComptimeResult::Type(meta_ty)))
                } else {
                    Ok(None)
                }
            }
        }
    }

    // todo: this is actually a great opportunity for fuzzing to make sure this function never
    // returns true when something was actually unsafe. the fuzzer has already been updated it just
    // needs to be used.
    pub(crate) fn is_safe_to_compile(
        &mut self,
        loc: ConcreteLoc,
        expr: Idx<hir::Expr>,
    ) -> InferResult<bool> {
        let mut checking_stack = vec![(
            loc,
            self.world_bodies[loc.file()]
                .descendants(
                    expr,
                    hir::DescentOpts::All {
                        include_lambdas: false,
                        include_post_exprs: false,
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

        // debug!("errors = {error_exprs:#?}");

        let mut checked = FxHashSet::default();
        checked.insert(loc);

        loop {
            let Some((loc, top_list)) = checking_stack.last_mut() else {
                break;
            };
            let loc = *loc;

            let Some(desc) = top_list.pop() else {
                checking_stack.pop();
                continue;
            };

            match desc {
                Descendant::PreExpr(expr) => {
                    // debug!("checking {} #{}", loc.debug(self.interner), expr.into_raw());

                    if error_exprs.contains(&(loc.file(), expr)) {
                        debug!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
                        return Ok(false);
                    }

                    if let Some(ty) = self.tys[loc].meta_ty(expr) {
                        if ty.is_unknown() {
                            debug!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
                            return Ok(false);
                        }

                        continue;
                    }

                    let Some(ty) = self.tys[loc].expr_tys.get(expr) else {
                        debug!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
                        return Ok(false);
                    };

                    if ty.is_unknown() {
                        debug!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
                        return Ok(false);
                    }

                    match ty.as_ref() {
                        Ty::NaivePolymorphicFunction { .. } => {
                            continue;
                        }
                        Ty::ConcreteFunction { fn_loc: loc, .. } => {
                            // debug!(
                            //     "{} <=> {}",
                            //     fn_loc.debug(self.interner),
                            //     loc.debug(self.interner)
                            // );

                            let Expr::Lambda(lambda) = &self.world_bodies[loc.file()][loc.expr()]
                            else {
                                unreachable!()
                            };

                            if checked.contains(&loc.wrap()) {
                                continue;
                            }

                            checked.insert(loc.wrap());

                            let lambda_body = &self.world_bodies[loc.file()][*lambda];

                            if !self.all_finished_locations.contains(&loc.wrap()) {
                                debug!(
                                    "submitting {} #{}",
                                    loc.debug(self.interner),
                                    expr.into_raw(),
                                );
                                return Err(vec![loc.wrap()]);
                            }

                            if lambda_body.body == hir::LambdaBody::Empty
                                && lambda_body.return_ty.is_none()
                            {
                                debug!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
                                return Ok(false);
                            }

                            if let hir::LambdaBody::Block(block) = lambda_body.body {
                                checking_stack.push((
                                    loc.wrap(),
                                    self.world_bodies[loc.file()]
                                        .descendants(
                                            block,
                                            hir::DescentOpts::All {
                                                include_lambdas: false,
                                                include_post_exprs: false,
                                                include_post_stmts: false,
                                            },
                                        )
                                        .collect(),
                                ));
                            }

                            continue;
                        }
                        _ => {}
                    }

                    match &self.world_bodies[loc.file()][expr] {
                        Expr::Missing => {
                            println!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
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
                            let new_loc = Fqn {
                                file: loc.file(),
                                name: name.name,
                            };

                            // generic functions should've been caught be the checks
                            // for ConcreteFunction and NaivePolymorphicFunction earlier
                            assert!(!self.world_bodies.has_polymorphic_body(new_loc.wrap()));
                            assert!(!matches!(**ty, Ty::NaivePolymorphicFunction { .. }));
                            assert!(!matches!(**ty, Ty::ConcreteFunction { .. }));

                            let new_loc = new_loc.make_concrete(None);

                            if checked.contains(&new_loc.wrap()) {
                                continue;
                            }

                            if self.world_bodies.global_is_extern(new_loc.to_naive()) {
                                continue;
                            }

                            match self
                                .tys
                                .try_naive(new_loc.to_naive().wrap(), self.world_bodies)
                            {
                                Ok(_) => {
                                    debug!("getting the body of {}", new_loc.debug(self.interner));
                                    let body = self.world_bodies.global_body(new_loc.to_naive());

                                    checking_stack.push((
                                        new_loc.wrap(),
                                        self.world_bodies[new_loc.file()]
                                            .descendants(
                                                body,
                                                hir::DescentOpts::All {
                                                    include_lambdas: false,
                                                    include_post_exprs: false,
                                                    include_post_stmts: false,
                                                },
                                            )
                                            .collect(),
                                    ));

                                    checked.insert(new_loc.wrap());
                                }
                                Err(NaiveLookupErr::NotFound) => {
                                    debug!(
                                        "submitting {} #{}",
                                        loc.debug(self.interner),
                                        expr.into_raw()
                                    );
                                    return Err(vec![new_loc.wrap()]);
                                }
                                Err(NaiveLookupErr::IsPolymorphic) => unreachable!(
                                    "the checks for naive and concrete fn earlier should've caught this"
                                ),
                            }
                        }
                        Expr::Param { .. } => {}
                        Expr::ComptimeParam { .. } => {}
                        Expr::InlineParam { .. } => {}
                        Expr::Member {
                            previous,
                            name: field,
                        } => {
                            let previous_ty = self.tys[loc][*previous];

                            if let Ty::File(file) = previous_ty.as_ref() {
                                let new_loc = Fqn {
                                    file: *file,
                                    name: field.name,
                                };

                                assert!(!matches!(
                                    self.tys.try_naive(new_loc.wrap(), self.world_bodies),
                                    Err(NaiveLookupErr::IsPolymorphic)
                                ));
                                let new_loc = new_loc.make_concrete(None);

                                // todo! there's no checking here

                                if checked.contains(&new_loc.wrap()) {
                                    continue;
                                }

                                checked.insert(new_loc.wrap());

                                if self.world_bodies.global_is_extern(new_loc.to_naive()) {
                                    continue;
                                }

                                match self.world_index.definition(new_loc.to_naive()) {
                                    hir::DefinitionStatus::Defined => {
                                        let mut deps = Vec::new();

                                        if !self.all_finished_locations.contains(&new_loc.wrap()) {
                                            deps.push(new_loc.wrap());
                                        }

                                        let body =
                                            self.world_bodies.global_body(new_loc.to_naive());

                                        // if let Expr::Lambda(lambda) =
                                        //     self.world_bodies.file()][body]
                                        // {
                                        //     let lambda = Inferrable::Lambda(FQLambda {
                                        //         file:.file(),
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
                                            debug!(
                                                "submitting {} #{}",
                                                new_loc.debug(self.interner),
                                                expr.into_raw()
                                            );
                                            return Err(deps);
                                        }

                                        checking_stack.push((
                                            new_loc.wrap(),
                                            self.world_bodies[new_loc.file()]
                                                .descendants(
                                                    body,
                                                    hir::DescentOpts::All {
                                                        include_lambdas: false,
                                                        include_post_exprs: false,
                                                        include_post_stmts: false,
                                                    },
                                                )
                                                .collect(),
                                        ));
                                    }
                                    _ => {
                                        debug!(
                                            "unsafe {} #{}",
                                            file.debug(self.interner),
                                            expr.into_raw()
                                        );
                                        return Ok(false);
                                    }
                                }
                            }
                        }
                        Expr::Call { callee, .. } => {
                            // I don't even know if this is possible.
                            // I'm gonna put an assert and test later
                            // TODO: test this
                            assert!(!matches!(
                                self.tys[loc][*callee].as_ref(),
                                Ty::NaivePolymorphicFunction { .. }
                            ));
                        }
                        Expr::Lambda(_) => unreachable!(
                            "Lambda at {} #{} with type {} wasn't handled",
                            loc.debug(self.interner),
                            expr.into_raw(),
                            ty.debug(self.interner, true)
                        ),
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
                Descendant::PostExpr(_) => unreachable!(),
                Descendant::PreStmt(stmt) => {
                    debug!(
                        "checking {} stmt#{}",
                        loc.debug(self.interner),
                        stmt.into_raw()
                    );
                    match &self.world_bodies[loc.file()][stmt] {
                        Stmt::Expr(_) => {}
                        Stmt::LocalDef(_) => {}
                        Stmt::Assign(_) => {}
                        Stmt::Break { label, .. } | Stmt::Continue { label, .. } => {
                            if label.is_none() {
                                debug!("unsafe {} #{}", loc.debug(self.interner), expr.into_raw());
                                return Ok(false);
                            }
                        }
                        Stmt::Defer { .. } => {}
                    }
                }
                Descendant::PostStmt(_) => unreachable!(),
            }
        }

        Ok(true)
    }
}

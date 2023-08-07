use hir_ty::ResolvedTy;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::FileType;
use inkwell::targets::TargetMachine;
use inkwell::types::{BasicMetadataTypeEnum, BasicType};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, GlobalValue, PointerValue,
};
use inkwell::{AddressSpace, IntPredicate};
use interner::Interner;
use la_arena::{Arena, Idx};
use rustc_hash::FxHashMap;
use std::path::Path;
use std::process::exit;
use std::{fs, str};

use crate::mangle::Mangle;
use crate::ty::ToCompType;

pub(crate) struct CodeGen<'a, 'ctx> {
    pub(crate) resolved_arena: &'a Arena<ResolvedTy>,
    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: &'a FxHashMap<hir::Name, hir::Bodies>,
    pub(crate) types_map: &'a FxHashMap<hir::Name, hir_ty::InferenceResult>,
    pub(crate) world_index: &'a hir::WorldIndex,

    pub(crate) context: &'ctx Context,
    pub(crate) module: &'a Module<'ctx>,
    pub(crate) builder_stack: Vec<Builder<'ctx>>,
    pub(crate) entry_point: hir::Fqn,
    pub(crate) functions_to_compile: Vec<hir::Fqn>,
    pub(crate) functions: FxHashMap<hir::Fqn, FunctionValue<'ctx>>,
    pub(crate) globals: FxHashMap<hir::Fqn, GlobalValue<'ctx>>,
    pub(crate) locals: FxHashMap<Idx<hir::LocalDef>, PointerValue<'ctx>>,
    pub(crate) function_stack: Vec<FunctionValue<'ctx>>,
    pub(crate) param_stack_map: Vec<Vec<Option<u32>>>,

    pub(crate) target_machine: &'a TargetMachine,
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub(crate) fn finish(
        mut self,
        source_file_name: &str,
        verbose: bool,
    ) -> Result<Vec<u8>, String> {
        assert!(self.functions_to_compile.contains(&self.entry_point));
        self.compile_queued_functions();
        assert!(self.functions.contains_key(&self.entry_point));
        self.generate_main_function();

        if verbose {
            println!("\n{}", self.module.print_to_string().to_string());
        }
        // ignore bc I don't care if the file already exists
        let _ = fs::create_dir("out");

        let file = format!(
            "out/{}.ll",
            self.module.get_name().to_str().unwrap_or(source_file_name)
        );
        fs::write(&file, self.module.print_to_string().to_string())
            .map_err(|why| format!("{} (\"{}\")", file, why))?;

        let file = format!(
            "out/{}.asm",
            self.module.get_name().to_str().unwrap_or(source_file_name)
        );
        self.target_machine
            .write_to_file(self.module, FileType::Assembly, Path::new(&file))
            .map_err(|why| format!("{} ({})", file, why))?;

        self.target_machine
            .write_to_memory_buffer(self.module, FileType::Object)
            .map_err(|why| format!("obj file ({})", why))
            .map(|buffer| buffer.as_slice().to_vec())
    }

    fn compile_queued_functions(&mut self) {
        while let Some(name) = self.functions_to_compile.pop() {
            self.compile_function(name);
            self.compile_queued_functions();
        }
    }

    fn generate_main_function(&mut self) {
        let fn_type = self.context.i32_type().fn_type(
            &[
                self.context.i32_type().into(),
                self.context
                    .i8_type() // char
                    .ptr_type(AddressSpace::default()) // char   []
                    .ptr_type(AddressSpace::default()) // char [][]
                    .into(),
            ],
            false,
        );

        let function = self.module.add_function("main", fn_type, None);

        let builder = self.context.create_builder();

        let entry_block = self.context.append_basic_block(function, "entry");

        builder.position_at_end(entry_block);

        let value = builder.build_call(
            *self.functions.get(&self.entry_point).unwrap(),
            &[],
            "call_entry_point",
        );

        let hir_def = self.world_index.get_definition(self.entry_point).unwrap();
        let hir_function = match hir_def {
            hir::Definition::Function(f) => f,
            _ => {
                println!("tried to use non-function as entry point");
                exit(1)
            }
        };

        if matches!(
            hir_function.return_ty,
            hir::TyWithRange::IInt { .. } | hir::TyWithRange::UInt { .. }
        ) {
            builder.build_return(Some(&value.try_as_basic_value().unwrap_left()));
        } else {
            builder.build_return(Some(&self.context.i32_type().const_int(0, false)));
        }
    }

    #[inline]
    fn current_function(&self) -> &FunctionValue<'ctx> {
        self.function_stack.last().unwrap()
    }

    #[inline]
    fn builder(&self) -> &Builder<'ctx> {
        self.builder_stack.last().unwrap()
    }

    fn create_alloca<T: BasicType<'ctx>>(&self, type_: T, name: &str) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self.current_function().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(type_, name)
    }

    fn compile_global(&mut self, fqn: hir::Fqn) {
        let signature = &self.types_map[&fqn.module][fqn]
            .as_global()
            .unwrap_or_else(|| {
                println!("tried to compile non-global as global");
                exit(1)
            });

        let global_ty = signature.ty.to_comp_type(self);

        if global_ty.is_void_type() {
            return;
        }

        let global = self.module.add_global(
            global_ty.into_basic_type(),
            None,
            &fqn.to_mangled_name(self.interner),
        );

        let hir_value = self.bodies_map[&fqn.module].global(fqn.name);

        let init = match self.compile_expr(fqn.module, hir_value) {
            Some(value) => value,
            None => todo!(),
        };

        global.set_initializer(&init);

        self.globals.insert(fqn, global);
    }

    fn compile_function(&mut self, fqn: hir::Fqn) {
        let signature = &self.types_map[&fqn.module][fqn]
            .as_function()
            .unwrap_or_else(|| {
                println!("tried to compile non-function as function");
                exit(1)
            });

        let mut param_map = Vec::new();

        let param_types: Vec<BasicMetadataTypeEnum> = signature
            .param_tys
            .iter()
            .filter_map(|param_ty| {
                let param_type = match param_ty {
                    hir_ty::ResolvedTy::Void { .. } => None,
                    other_ty => Some(other_ty.to_comp_type(self).into_basic_type().into()),
                };
                param_map.push(param_type.map(|_| 0)); // 0 is a temporary value
                param_type
            })
            .collect();
        let param_types = param_types.as_slice();

        param_map
            .iter_mut()
            .filter(|op| op.is_some())
            .enumerate()
            .for_each(|(new_idx, op)| {
                *op = Some(new_idx as u32);
            });
        self.param_stack_map.push(param_map);

        let fn_type = signature.return_ty.to_comp_type(self).fn_type(param_types);

        let function = self
            .module
            .add_function(&fqn.to_mangled_name(self.interner), fn_type, None);
        self.functions.insert(fqn, function);
        self.function_stack.push(function);

        self.builder_stack.push(self.context.create_builder());

        let entry_block = self.context.append_basic_block(function, "entry");

        self.builder().position_at_end(entry_block);

        let hir_body = self.bodies_map[&fqn.module].function_body(fqn.name);

        match self.compile_expr(fqn.module, hir_body) {
            Some(body) => self.builder().build_return(Some(&body)),
            None => self.builder().build_return(None),
        };

        self.builder_stack.pop();
        self.function_stack.pop();
        self.param_stack_map.pop();
    }

    fn compile_stmt(&mut self, module: hir::Name, stmt: &Idx<hir::Stmt>) {
        match self.bodies_map[&module][*stmt] {
            hir::Stmt::Expr(expr) => {
                match self.types_map[&module][expr] {
                    hir_ty::ResolvedTy::Unknown => unreachable!(),
                    hir_ty::ResolvedTy::Named(_) => todo!(),
                    _ => {
                        self.compile_expr(module, expr);
                    }
                };
            }
            hir::Stmt::LocalDef(local_def) => {
                let value = self.bodies_map[&module][local_def].value;

                let value = if let Some(val) = self.compile_expr(module, value) {
                    val
                } else {
                    // ignore void defs
                    return;
                };

                let ty = self.types_map[&module][local_def]
                    .to_comp_type(self)
                    .into_basic_type();

                let var = self.create_alloca(ty, &format!("l{}", local_def.into_raw()));
                self.locals.insert(local_def, var);
                self.builder().build_store(var, value);
            }
            hir::Stmt::LocalSet(local_set) => {
                let value = self.bodies_map[&module][local_set].value;
                let value = if let Some(val) = self.compile_expr(module, value) {
                    val
                } else {
                    return;
                };

                let def_to_set = self.bodies_map[&module][local_set].local_def.unwrap();
                let def_to_set = self.locals.get(&def_to_set).unwrap();

                self.builder().build_store(*def_to_set, value);
            }
        }
    }

    fn compile_expr(
        &mut self,
        module: hir::Name,
        expr: Idx<hir::Expr>,
    ) -> Option<BasicValueEnum<'ctx>> {
        self.compile_expr_with_args(module, expr, true)
    }

    fn compile_expr_with_args(
        &mut self,
        module: hir::Name,
        expr: Idx<hir::Expr>,
        deref_any_ptrs: bool,
    ) -> Option<BasicValueEnum<'ctx>> {
        match self.bodies_map[&module][expr].clone() {
            hir::Expr::Missing => unreachable!(),
            hir::Expr::IntLiteral(n) => Some(
                self.types_map[&module][expr]
                    .to_comp_type(self)
                    .into_basic_type()
                    .into_int_type()
                    .const_int(n, false)
                    .as_basic_value_enum(),
            ),
            hir::Expr::BoolLiteral(b) => Some(
                self.context
                    .bool_type()
                    .const_int(b as u64, false)
                    .as_basic_value_enum(),
            ),
            hir::Expr::StringLiteral(text) => {
                let global = unsafe { self.builder().build_global_string(&text, ".str") };
                global.set_linkage(Linkage::Private);
                global.set_unnamed_addr(false);
                global.set_constant(true);

                Some(global.as_basic_value_enum())
            }
            hir::Expr::Array { items, .. } => {
                let array_ty = self.types_map[&module][expr]
                    .to_comp_type(self)
                    .into_basic_type()
                    .into_array_type();

                let array = self.create_alloca(array_ty, "array");

                for (idx, item) in items.iter().enumerate() {
                    let first = unsafe {
                        array.const_in_bounds_gep(&[
                            self.context.i64_type().const_int(0, true), // the first index points to the array pointer itself (`array` is a pointer to an array value, not an array value itself)
                            self.context.i64_type().const_int(idx as u64, true), // the second index points to the actual index of that array value
                        ])
                    };

                    let value = self.compile_expr(module, *item).unwrap();

                    self.builder().build_store(first, value);
                }

                if deref_any_ptrs {
                    Some(self.builder().build_load(array, ".arr_l"))
                } else {
                    Some(array.as_basic_value_enum())
                }
            }
            hir::Expr::Index { array, index } => {
                // hir_ty has already checked that this is a uint
                let index = self.compile_expr(module, index).unwrap().into_int_value();

                let array = self.compile_expr_with_args(module, array, false).unwrap();
                let array = if array.is_pointer_value() {
                    array.into_pointer_value()
                } else if array.is_array_value() {
                    let alloc = self.create_alloca(array.get_type(), "temp");
                    self.builder().build_store(alloc, array);
                    alloc
                } else {
                    unreachable!()
                };

                let value_ptr = unsafe {
                    array.const_in_bounds_gep(&[
                        self.context.i64_type().const_int(0, true), // the first index points to the array pointer itself (`array` is a pointer to an array value, not an array value itself)
                        index,
                    ])
                };

                Some(self.builder().build_load(value_ptr, "i_"))
            }
            hir::Expr::Cast {
                expr: inner_expr, ..
            } => {
                let inner = self.compile_expr(module, inner_expr);
                let cast_from = &self.types_map[&module][inner_expr];
                let cast_to = &self.types_map[&module][expr];

                println!("{:?} as {:?}", cast_from, cast_to);

                // check if casting is irrelevant
                if cast_from.is_functionally_equivalent_to(*cast_to, self.resolved_arena) {
                    println!("irrelevant");
                    inner
                } else {
                    inner.map(|inner| {
                        self.builder()
                            .build_int_cast_sign_flag(
                                inner.into_int_value(),
                                cast_to.to_comp_type(self).into_basic_type().into_int_type(),
                                true,
                                ".cast",
                            )
                            .as_basic_value_enum()
                    })
                }
            }
            hir::Expr::Ref { expr } => {
                let inner = self.compile_expr(module, expr).unwrap();

                let alloc = self.create_alloca(inner.get_type(), "temp_alloc");
                self.builder().build_store(alloc, inner);
                Some(alloc.as_basic_value_enum())
            }
            hir::Expr::Deref { pointer } => {
                let inner = self
                    .compile_expr(module, pointer)
                    .unwrap()
                    .into_pointer_value();

                Some(self.builder().build_load(inner, "deref"))
            }
            hir::Expr::Binary {
                lhs: lhs_expr,
                rhs: rhs_expr,
                op,
            } => {
                let mut lhs = self
                    .compile_expr(module, lhs_expr)
                    .unwrap()
                    .into_int_value();
                let mut rhs = self
                    .compile_expr(module, rhs_expr)
                    .unwrap()
                    .into_int_value();

                // LLVM will only change the type of the operands instead of zext
                let lhs_bit_width = lhs.get_type().get_bit_width();
                let rhs_bit_width = rhs.get_type().get_bit_width();
                if lhs_bit_width != rhs_bit_width {
                    let max_bit_width = lhs_bit_width.max(rhs_bit_width);
                    lhs = self.builder().build_int_z_extend_or_bit_cast(
                        lhs,
                        self.context.custom_width_int_type(max_bit_width),
                        ".lhscast",
                    );
                    rhs = self.builder().build_int_z_extend_or_bit_cast(
                        rhs,
                        self.context.custom_width_int_type(max_bit_width),
                        ".rhscast",
                    );
                }

                Some(match op {
                    hir::BinaryOp::Add => self.builder().build_int_add(lhs, rhs, "tmp_add").into(),
                    hir::BinaryOp::Sub => self.builder().build_int_sub(lhs, rhs, "tmp_sub").into(),
                    hir::BinaryOp::Mul => self.builder().build_int_mul(lhs, rhs, "tmp_mul").into(),
                    hir::BinaryOp::Div => match self.types_map[&module][expr] {
                        hir_ty::ResolvedTy::IInt(_) => self
                            .builder()
                            .build_int_signed_div(lhs, rhs, "tmp_div")
                            .into(),
                        hir_ty::ResolvedTy::UInt(_) => self
                            .builder()
                            .build_int_unsigned_div(lhs, rhs, "tmp_div")
                            .into(),
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Lt => match self.types_map[&module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::SLT, lhs, rhs, "tmp_cmp")
                            .into(),
                        hir_ty::ResolvedTy::UInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::ULT, lhs, rhs, "tmp_cmp")
                            .into(),
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Gt => match self.types_map[&module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::SGT, lhs, rhs, "tmp_cmp")
                            .into(),
                        hir_ty::ResolvedTy::UInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::UGT, lhs, rhs, "tmp_cmp")
                            .into(),
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Le => match self.types_map[&module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::SLE, lhs, rhs, "tmp_cmp")
                            .into(),
                        hir_ty::ResolvedTy::UInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::ULE, lhs, rhs, "tmp_cmp")
                            .into(),
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Ge => match self.types_map[&module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::SGE, lhs, rhs, "tmp_cmp")
                            .into(),
                        hir_ty::ResolvedTy::UInt(_) => self
                            .builder()
                            .build_int_compare(IntPredicate::UGE, lhs, rhs, "tmp_cmp")
                            .into(),
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Eq => self
                        .builder()
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "tmp_cmp")
                        .into(),
                    hir::BinaryOp::Ne => self
                        .builder()
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "tmp_cmp")
                        .into(),
                    hir::BinaryOp::And => self.builder().build_and(lhs, rhs, "tmp_and").into(),
                    hir::BinaryOp::Or => self.builder().build_or(lhs, rhs, "tmp_or").into(),
                })
            }
            hir::Expr::Unary { expr, op } => {
                let expr = self.compile_expr(module, expr).unwrap().into_int_value();
                match op {
                    hir::UnaryOp::Pos => Some(expr.into()),
                    hir::UnaryOp::Neg => Some(self.builder().build_int_neg(expr, "tmp_neg").into()),
                    hir::UnaryOp::Not => Some(self.builder().build_not(expr, "tmp_not").into()),
                }
            }
            hir::Expr::Call { path, args } => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let function = match self.functions.get(&fqn) {
                    Some(function) => *function,
                    None => {
                        if self.interner.lookup(fqn.name.0) == "printf" {
                            if let Some(printf) = self.module.get_function("printf") {
                                self.functions.insert(fqn, printf);
                            } else {
                                let fn_type = self.context.void_type().fn_type(
                                    &[ResolvedTy::String
                                        .to_comp_type(self)
                                        .into_basic_type()
                                        .into()],
                                    true,
                                );
                                let printf = self.module.add_function("printf", fn_type, None);
                                self.functions.insert(fqn, printf);
                            }
                            *self.functions.get(&fqn).unwrap()
                        } else if self.interner.lookup(fqn.name.0) == "exit" {
                            if let Some(exit) = self.module.get_function("exit") {
                                self.functions.insert(fqn, exit);
                            } else {
                                let fn_type = self
                                    .context
                                    .void_type()
                                    .fn_type(&[self.context.i32_type().into()], false);
                                let exit = self.module.add_function("exit", fn_type, None);
                                self.functions.insert(fqn, exit);
                            }
                            *self.functions.get(&fqn).unwrap()
                        } else {
                            self.compile_function(fqn);
                            *self.functions.get(&fqn).unwrap()
                        }
                    }
                };

                let mut argsv: Vec<BasicMetadataValueEnum> = Vec::with_capacity(args.len());

                for arg in args {
                    if let Some(val) = match self.types_map[&module][arg] {
                        hir_ty::ResolvedTy::Unknown => todo!(),
                        hir_ty::ResolvedTy::Named(_) => todo!(),
                        _ => self.compile_expr(module, arg).map(|val| val.into()),
                    } {
                        argsv.push(val);
                    }
                }

                self.builder()
                    .build_call(function, argsv.as_slice(), "tmp_call")
                    .try_as_basic_value()
                    .left()
            }
            hir::Expr::Global(path) => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let global = match self.globals.get(&fqn) {
                    Some(global) => *global,
                    None => {
                        // todo: fix recursive definition stack overflow
                        // a : i32 : b;
                        // b : i32 : a;
                        self.compile_global(fqn);
                        match self.globals.get(&fqn) {
                            Some(global) => *global,
                            None => return None,
                        }
                    }
                };

                if deref_any_ptrs {
                    Some(self.builder_stack.last().unwrap().build_load(
                        global.as_pointer_value(),
                        &format!("{}_", self.interner.lookup(fqn.name.0)),
                    ))
                } else {
                    Some(global.as_pointer_value().as_basic_value_enum())
                }
            }
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.compile_stmt(module, &stmt);
                }

                if let Some(val) = tail_expr {
                    self.compile_expr_with_args(module, val, deref_any_ptrs)
                } else {
                    None
                }
            }
            hir::Expr::If {
                condition,
                body,
                else_branch,
            } => {
                let parent = *self.current_function();

                let cond = self
                    .compile_expr(module, condition)
                    .unwrap()
                    .into_int_value();

                // build branch
                let then_block = self.context.append_basic_block(parent, "then");
                let else_block = self.context.append_basic_block(parent, "else");
                let cont_block = self.context.append_basic_block(parent, "cont");

                self.builder()
                    .build_conditional_branch(cond, then_block, else_block);

                // build then block
                self.builder().position_at_end(then_block);
                let then_value = self.compile_expr(module, body);
                self.builder().build_unconditional_branch(cont_block);

                let then_block = self.builder().get_insert_block().unwrap();

                // build else block
                self.builder().position_at_end(else_block);
                let else_value = if let Some(else_branch) = else_branch {
                    self.compile_expr(module, else_branch)
                } else {
                    None
                };
                self.builder().build_unconditional_branch(cont_block);

                let else_block = self.builder().get_insert_block().unwrap();

                // emit merge block
                self.builder().position_at_end(cont_block);

                if let Some(else_value) = else_value {
                    let phi = self
                        .builder()
                        .build_phi(then_value.unwrap().get_type(), "iftmp");

                    phi.add_incoming(&[
                        (&then_value.unwrap(), then_block),
                        (&else_value, else_block),
                    ]);

                    Some(phi.as_basic_value())
                } else {
                    None
                }
            }
            hir::Expr::While { condition, body } => {
                let parent = *self.current_function();

                // build branch
                let cond_block = self.context.append_basic_block(parent, "cond");
                let loop_block = self.context.append_basic_block(parent, "loop");
                let break_block = self.context.append_basic_block(parent, "break");

                self.builder().build_unconditional_branch(cond_block);

                // build cond block
                self.builder().position_at_end(cond_block);
                match condition {
                    Some(condition) => {
                        let condition = self
                            .compile_expr(module, condition)
                            .unwrap()
                            .into_int_value();
                        self.builder()
                            .build_conditional_branch(condition, loop_block, break_block);
                    }
                    None => {
                        self.builder().build_unconditional_branch(loop_block);
                    }
                };

                // build loop block
                self.builder().position_at_end(loop_block);
                let loop_val = self.compile_expr(module, body);
                self.builder().build_unconditional_branch(cond_block);

                // emit merge block
                self.builder().position_at_end(break_block);

                loop_val
            }
            hir::Expr::Local(local_def) => {
                if let Some(var) = self.locals.get(&local_def) {
                    if deref_any_ptrs {
                        Some(
                            self.builder_stack
                                .last()
                                .unwrap()
                                .build_load(*var, &format!("l{}_", local_def.into_raw())),
                        )
                    } else {
                        Some((*var).as_basic_value_enum())
                    }
                } else {
                    None
                }
            }
            hir::Expr::Param { idx } => self
                .param_stack_map
                .last()
                .unwrap() // there will always be a function in the stack here
                .get(idx as usize)
                .unwrap() // parameters have been checked earlier
                .map(|real_idx| self.function_stack.last().unwrap().get_nth_param(real_idx))
                .flatten(),
            hir::Expr::PrimitiveTy { .. } => None,
        }
    }
}

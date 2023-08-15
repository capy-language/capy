use std::collections::VecDeque;

use cranelift::{
    codegen::ir::Endianness,
    prelude::{
        types, EntityRef, FunctionBuilder, InstBuilder, IntCC, MemFlags, StackSlotData,
        StackSlotKind, Value, Variable,
    },
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use hir::{LocalDef, UIDGenerator};
use hir_ty::ResolvedTy;
use interner::Interner;
use la_arena::{Arena, Idx};
use rustc_hash::FxHashMap;

use crate::{
    convert::{ToCompSize, ToCompType},
    gen,
    mangle::Mangle,
    CraneliftSignature,
};

pub(crate) struct FunctionCompiler<'a> {
    pub(crate) fqn: hir::Fqn, // the fqn of this function
    pub(crate) signature: CraneliftSignature,

    pub(crate) resolved_arena: &'a Arena<ResolvedTy>,
    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: &'a FxHashMap<hir::Name, hir::Bodies>,
    pub(crate) tys: &'a hir_ty::InferenceResult,

    pub(crate) builder: FunctionBuilder<'a>,
    pub(crate) module: &'a mut dyn Module,
    pub(crate) data_description: &'a mut DataDescription,

    pub(crate) functions_to_compile: &'a mut VecDeque<hir::Fqn>,

    // globals
    pub(crate) functions: &'a mut FxHashMap<hir::Fqn, FuncId>,
    pub(crate) globals: &'a mut FxHashMap<hir::Fqn, DataId>,
    pub(crate) str_id_gen: &'a mut UIDGenerator,

    // variables
    pub(crate) var_id_gen: UIDGenerator,
    pub(crate) locals: FxHashMap<Idx<LocalDef>, Variable>,
    pub(crate) params: FxHashMap<u64, Variable>,
}

impl FunctionCompiler<'_> {
    pub(crate) fn finish(mut self, return_ty: ResolvedTy, new_idx_to_old_idx: FxHashMap<u64, u64>) {
        // Create the entry block, to start emitting code in.
        let entry_block = self.builder.create_block();

        self.builder
            .append_block_params_for_function_params(entry_block);

        self.builder.switch_to_block(entry_block);
        self.builder.seal_block(entry_block);

        let mut dest_param = None;

        for (idx, param) in self.signature.params.iter().enumerate() {
            let param_ty = param.value_type;

            let value = self.builder.block_params(entry_block)[idx];

            let var = Variable::new(self.var_id_gen.generate_unique_id() as usize);

            if new_idx_to_old_idx.contains_key(&(idx as u64)) {
                self.params.insert(new_idx_to_old_idx[&(idx as u64)], var);
            } else {
                let old_dest_param = dest_param.replace(var);
                assert!(old_dest_param.is_none());
            }

            self.builder.declare_var(var, param_ty);

            self.builder.def_var(var, value);
        }

        let hir_body = self.bodies_map[&self.fqn.module].function_body(self.fqn.name);

        match self.compile_expr(hir_body) {
            Some(body) => {
                if return_ty.is_array(self.resolved_arena) {
                    let dest = self.builder.use_var(dest_param.unwrap());

                    let array_size = return_ty.get_size_in_bytes(self.module, self.resolved_arena);
                    let array_size = self.builder.ins().iconst(
                        self.module.target_config().pointer_type(),
                        array_size as i64,
                    );

                    self.builder
                        .call_memcpy(self.module.target_config(), dest, body, array_size);

                    self.builder.ins().return_(&[dest])
                } else if let Some(return_int_ty) = return_ty
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_int_type()
                {
                    let body_int_ty = self.tys[self.fqn.module][hir_body]
                        .to_comp_type(self.module, self.resolved_arena)
                        .into_int_type()
                        .unwrap();

                    let cast = match body_int_ty.bit_width.cmp(&return_int_ty.bit_width) {
                        std::cmp::Ordering::Less if return_int_ty.signed && body_int_ty.signed => {
                            self.builder.ins().sextend(return_int_ty.ty, body)
                        }
                        std::cmp::Ordering::Less => {
                            self.builder.ins().uextend(return_int_ty.ty, body)
                        }
                        std::cmp::Ordering::Equal => body,
                        std::cmp::Ordering::Greater => {
                            self.builder.ins().ireduce(return_int_ty.ty, body)
                        }
                    };

                    self.builder.ins().return_(&[cast])
                } else {
                    self.builder.ins().return_(&[body])
                }
            }
            None => self.builder.ins().return_(&[]),
        };

        self.builder.seal_all_blocks();
        self.builder.finalize();
    }

    fn expr_to_const_data(&mut self, module: hir::Name, expr: Idx<hir::Expr>) -> Vec<u8> {
        match self.bodies_map[&module][expr].clone() {
            hir::Expr::Missing => todo!(),
            hir::Expr::IntLiteral(n) => {
                match (
                    self.tys[module][expr]
                        .to_comp_type(self.module, self.resolved_arena)
                        .into_int_type()
                        .unwrap()
                        .bit_width,
                    self.module.isa().endianness(),
                ) {
                    (8, Endianness::Little) => (n as u8).to_le_bytes().to_vec(),
                    (8, Endianness::Big) => (n as u8).to_be_bytes().to_vec(),
                    (16, Endianness::Little) => (n as u16).to_le_bytes().to_vec(),
                    (16, Endianness::Big) => (n as u16).to_be_bytes().to_vec(),
                    (32, Endianness::Little) => (n as u32).to_le_bytes().to_vec(),
                    (32, Endianness::Big) => (n as u32).to_be_bytes().to_vec(),
                    #[allow(clippy::unnecessary_cast)]
                    (64, Endianness::Little) => (n as u64).to_le_bytes().to_vec(),
                    #[allow(clippy::unnecessary_cast)]
                    (64, Endianness::Big) => (n as u64).to_be_bytes().to_vec(),
                    (128, Endianness::Little) => (n as u128).to_le_bytes().to_vec(),
                    (128, Endianness::Big) => (n as u128).to_be_bytes().to_vec(),
                    _ => unreachable!(),
                }
            }
            hir::Expr::BoolLiteral(b) => {
                vec![b as u8]
            }
            hir::Expr::StringLiteral(mut text) => {
                text.push('\0');
                text.into_bytes()
            }
            hir::Expr::Array { items, .. } => {
                assert_ne!(items.len(), 0);

                let item_size =
                    self.tys[module][items[0]].get_size_in_bytes(self.module, self.resolved_arena);

                let mut array = Vec::with_capacity(item_size as usize * items.len());

                for item in items {
                    let item = self.expr_to_const_data(module, item);

                    array.extend(item.into_iter());
                }

                array
            }
            _ => panic!("global with non-constant definition"),
        }
    }

    fn compile_global(&mut self, fqn: hir::Fqn) -> DataId {
        if let Some(global) = self.globals.get(&fqn) {
            return *global;
        }

        let value = self.bodies_map[&fqn.module].global(fqn.name);
        let value_bytes = self.expr_to_const_data(fqn.module, value);

        let global = self.create_global_data(&fqn.to_mangled_name(self.interner), value_bytes);

        self.globals.insert(fqn, global);

        global
    }

    fn create_global_data(&mut self, name: &str, data: Vec<u8>) -> DataId {
        self.data_description.define(data.into_boxed_slice());
        let id = self
            .module
            .declare_data(name, Linkage::Export, true, false)
            .expect("error declaring data");

        self.module
            .define_data(id, self.data_description)
            .expect("error defining data");
        self.data_description.clear();

        id
    }

    fn create_global_str(&mut self, mut text: String) -> DataId {
        text.push('\0');
        let name = format!(".str{}", self.str_id_gen.generate_unique_id());
        self.create_global_data(&name, text.into_bytes())
    }

    fn get_func_id(&mut self, fqn: hir::Fqn) -> FuncId {
        gen::get_func_id(
            self.module,
            self.functions,
            self.functions_to_compile,
            self.tys,
            self.resolved_arena,
            self.interner,
            fqn,
        )
    }

    fn compile_stmt(&mut self, stmt: &Idx<hir::Stmt>) {
        match self.bodies_map[&self.fqn.module][*stmt] {
            hir::Stmt::Expr(expr) => {
                match self.tys[self.fqn.module][expr] {
                    hir_ty::ResolvedTy::Unknown => unreachable!(),
                    hir_ty::ResolvedTy::Named(_) => todo!(),
                    _ => {
                        self.compile_expr(expr);
                    }
                };
            }
            hir::Stmt::LocalDef(local_def) => {
                let value = self.bodies_map[&self.fqn.module][local_def].value;

                let value = if let Some(val) = self.compile_expr(value) {
                    val
                } else {
                    // ignore void definitions
                    return;
                };

                let ty = self.tys[self.fqn.module][local_def]
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_real_type()
                    .unwrap();

                // todo: defs should be on the stack
                let var = Variable::new(self.var_id_gen.generate_unique_id() as usize);

                self.locals.insert(local_def, var);
                self.builder.declare_var(var, ty);

                self.builder.def_var(var, value);
            }
            hir::Stmt::LocalSet(local_set) => {
                let value = self.bodies_map[&self.fqn.module][local_set].value;
                let value = if let Some(val) = self.compile_expr(value) {
                    val
                } else {
                    return;
                };

                let local = self.bodies_map[&self.fqn.module][local_set]
                    .local_def
                    .unwrap();
                let local = self.locals.get(&local).unwrap();

                self.builder.def_var(*local, value);
            }
        }
    }

    fn compile_array_items(&mut self, items: Vec<Idx<hir::Expr>>, stack_addr: Value, offset: i32) {
        assert!(!items.is_empty());

        let inner_ty = self.tys[self.fqn.module][items[0]];
        let inner_size = inner_ty.get_size_in_bytes(self.module, self.resolved_arena);

        for (idx, item) in items.iter().enumerate() {
            match self.bodies_map[&self.fqn.module][*item].clone() {
                hir::Expr::Array { items, .. } => self.compile_array_items(
                    items,
                    stack_addr,
                    offset + (inner_size as i32 * idx as i32),
                ),
                _ if inner_ty.is_array(self.resolved_arena) => {
                    let far_off_array = self.compile_expr(*item).unwrap();

                    let offset = self.builder.ins().iconst(
                        self.module.target_config().pointer_type(),
                        offset as i64 + (inner_size as i64 * idx as i64),
                    );

                    let actual_addr = self.builder.ins().iadd(stack_addr, offset);

                    let size = self.builder.ins().iconst(
                        self.module.target_config().pointer_type(),
                        inner_size as i64,
                    );

                    self.builder.call_memcpy(
                        self.module.target_config(),
                        actual_addr,
                        far_off_array,
                        size,
                    )
                }
                _ => {
                    let item = self.compile_expr(*item).unwrap();

                    self.builder.ins().store(
                        MemFlags::new().with_aligned(),
                        item,
                        stack_addr,
                        offset + (inner_size as i32 * idx as i32),
                    );
                }
            };
        }
    }

    fn compile_expr(&mut self, expr: Idx<hir::Expr>) -> Option<Value> {
        self.compile_expr_with_args(expr, false)
    }

    fn compile_expr_with_args(&mut self, expr: Idx<hir::Expr>, _no_deref: bool) -> Option<Value> {
        match self.bodies_map[&self.fqn.module][expr].clone() {
            hir::Expr::Missing => unreachable!(),
            hir::Expr::IntLiteral(n) => Some(
                self.builder.ins().iconst(
                    self.tys[self.fqn.module][expr]
                        .to_comp_type(self.module, self.resolved_arena)
                        .into_real_type()
                        .unwrap(),
                    n as i64,
                ),
            ),
            hir::Expr::BoolLiteral(b) => Some(self.builder.ins().iconst(types::I8, b as i64)),
            hir::Expr::StringLiteral(text) => {
                let data = self.create_global_str(text);

                let local_id = self.module.declare_data_in_func(data, self.builder.func);

                let pointer = self.module.target_config().pointer_type();
                Some(self.builder.ins().symbol_value(pointer, local_id))
            }
            hir::Expr::Array { items, .. } => {
                if self.tys[self.fqn.module][expr].is_empty(self.resolved_arena) {
                    return None;
                }

                let array_size = self.tys[self.fqn.module][expr]
                    .get_size_in_bytes(self.module, self.resolved_arena);

                let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: array_size,
                });

                let stack_addr = self.builder.ins().stack_addr(
                    self.module.target_config().pointer_type(),
                    stack_slot,
                    0,
                );

                self.compile_array_items(items, stack_addr, 0);

                Some(stack_addr)
            }
            hir::Expr::Index { array, index } => {
                if self.tys[self.fqn.module][expr].is_empty(self.resolved_arena) {
                    return None;
                }

                let array = self.compile_expr(array).unwrap(); // this will be usize

                let index_ty = self.tys[self.fqn.module][index]
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_int_type()
                    .unwrap();

                let index = self.compile_expr(index).unwrap(); // this might be less than usize

                let naive_index = match index_ty
                    .bit_width
                    .cmp(&self.module.target_config().pointer_bits())
                {
                    std::cmp::Ordering::Less => self
                        .builder
                        .ins()
                        .uextend(self.module.target_config().pointer_type(), index),
                    std::cmp::Ordering::Equal => index,
                    std::cmp::Ordering::Greater => self
                        .builder
                        .ins()
                        .ireduce(self.module.target_config().pointer_type(), index),
                };

                // now we have to align the index, the elements of the array only start every
                // so many bytes (4 bytes for i32, 8 bytes for i64)
                // So the index has to be multiplied by the element size
                let element_ty = self.tys[self.fqn.module][expr];
                let element_size = element_ty.get_size_in_bytes(self.module, self.resolved_arena);
                let element_size = self.builder.ins().iconst(
                    self.module.target_config().pointer_type(),
                    element_size as i64,
                );

                let proper_index = self.builder.ins().imul(naive_index, element_size);

                let proper_addr = self.builder.ins().iadd(array, proper_index);

                if element_ty.is_array(self.resolved_arena) {
                    Some(proper_addr)
                } else {
                    Some(
                        self.builder.ins().load(
                            element_ty
                                .to_comp_type(self.module, self.resolved_arena)
                                .into_real_type()
                                .unwrap(),
                            MemFlags::new().with_aligned(),
                            proper_addr,
                            0,
                        ),
                    )
                }
            }
            hir::Expr::Cast {
                expr: inner_expr, ..
            } => {
                let inner = self.compile_expr(inner_expr);
                let cast_from = match self.tys[self.fqn.module][inner_expr]
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_int_type()
                {
                    Some(int_ty) => int_ty,
                    None => return inner,
                };
                let cast_to = self.tys[self.fqn.module][expr]
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_int_type()
                    .unwrap();

                // println!("{:?} as {:?}", cast_from, cast_to);

                // check if casting is irrelevant
                if cast_from.bit_width == cast_to.bit_width {
                    // println!("irrelevant");
                    inner
                } else {
                    inner.map(|inner| {
                        // if the inner type is getting larger
                        if cast_from.bit_width < cast_to.bit_width {
                            if cast_from.signed && cast_to.signed {
                                self.builder.ins().sextend(cast_to.ty, inner)
                            } else {
                                self.builder.ins().uextend(cast_to.ty, inner)
                            }
                        } else {
                            self.builder.ins().ireduce(cast_to.ty, inner)
                        }
                    })
                }
            }
            hir::Expr::Ref { expr } => {
                let inner_size = self.tys[self.fqn.module][expr]
                    .get_size_in_bytes(self.module, self.resolved_arena);

                // println!("{:?} = {inner_size}", self.tys[self.fqn.module][expr]);

                let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: inner_size,
                });

                let expr = self.compile_expr(expr).unwrap();

                self.builder.ins().stack_store(expr, stack_slot, 0);

                Some(self.builder.ins().stack_addr(
                    self.module.target_config().pointer_type(),
                    stack_slot,
                    0,
                ))
            }
            hir::Expr::Deref { pointer } => {
                let self_ty = self.tys[self.fqn.module][expr]
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_real_type()
                    .unwrap();
                let pointer = self.compile_expr(pointer)?;

                Some(
                    self.builder
                        .ins()
                        .load(self_ty, MemFlags::trusted(), pointer, 0),
                )
            }
            hir::Expr::Binary {
                lhs: lhs_expr,
                rhs: rhs_expr,
                op,
            } => {
                let lhs = self.compile_expr(lhs_expr).unwrap();
                let rhs = self.compile_expr(rhs_expr).unwrap();

                Some(match op {
                    hir::BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
                    hir::BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
                    hir::BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
                    hir::BinaryOp::Div => match self.tys[self.fqn.module][expr] {
                        hir_ty::ResolvedTy::IInt(_) => self.builder.ins().sdiv(lhs, rhs),
                        hir_ty::ResolvedTy::UInt(_) => self.builder.ins().udiv(lhs, rhs),
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Lt => match self.tys[self.fqn.module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => {
                            self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs)
                        }
                        hir_ty::ResolvedTy::UInt(_) => {
                            self.builder.ins().icmp(IntCC::UnsignedLessThan, lhs, rhs)
                        }
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Gt => match self.tys[self.fqn.module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => {
                            self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs)
                        }
                        hir_ty::ResolvedTy::UInt(_) => {
                            self.builder
                                .ins()
                                .icmp(IntCC::UnsignedGreaterThan, lhs, rhs)
                        }
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Le => match self.tys[self.fqn.module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => {
                            self.builder
                                .ins()
                                .icmp(IntCC::SignedLessThanOrEqual, lhs, rhs)
                        }
                        hir_ty::ResolvedTy::UInt(_) => {
                            self.builder
                                .ins()
                                .icmp(IntCC::UnsignedLessThanOrEqual, lhs, rhs)
                        }
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Ge => match self.tys[self.fqn.module][lhs_expr] {
                        hir_ty::ResolvedTy::IInt(_) => {
                            self.builder
                                .ins()
                                .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs)
                        }
                        hir_ty::ResolvedTy::UInt(_) => {
                            self.builder
                                .ins()
                                .icmp(IntCC::UnsignedGreaterThanOrEqual, lhs, rhs)
                        }
                        _ => unreachable!(),
                    },
                    hir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, lhs, rhs),
                    hir::BinaryOp::Ne => self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs),
                    hir::BinaryOp::And => self.builder.ins().band(lhs, rhs),
                    hir::BinaryOp::Or => self.builder.ins().bor(lhs, rhs),
                })
            }
            hir::Expr::Unary { expr, op } => {
                let expr = self.compile_expr(expr).unwrap();
                match op {
                    hir::UnaryOp::Pos => Some(expr),
                    hir::UnaryOp::Neg => Some(self.builder.ins().ineg(expr)),
                    hir::UnaryOp::Not => Some(self.builder.ins().bnot(expr)),
                }
            }
            hir::Expr::Call { path, args } => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn {
                        module: self.fqn.module,
                        name,
                    },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let func = self.get_func_id(fqn);
                let local_func = self.module.declare_func_in_func(func, self.builder.func);

                let mut arg_values = args
                    .iter()
                    .filter_map(|arg| match self.tys[self.fqn.module][*arg] {
                        hir_ty::ResolvedTy::Unknown => todo!(),
                        hir_ty::ResolvedTy::Named(_) => todo!(),
                        _ => self.compile_expr(*arg), // filter_map removes the void values
                    })
                    .collect::<Vec<_>>();

                let signature = self.tys[fqn].as_function().unwrap_or_else(|| {
                    panic!("tried to compile non-function as function");
                });

                if signature.return_ty.is_array(self.resolved_arena) {
                    let array_size = signature
                        .return_ty
                        .get_size_in_bytes(self.module, self.resolved_arena);

                    let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                        kind: StackSlotKind::ExplicitSlot,
                        size: array_size,
                    });
                    let stack_slot_addr = self.builder.ins().stack_addr(
                        self.module.target_config().pointer_type(),
                        stack_slot,
                        0,
                    );

                    arg_values.push(stack_slot_addr);
                }

                let call = self.builder.ins().call(local_func, &arg_values);

                if signature.return_ty.is_empty(self.resolved_arena) {
                    None
                } else {
                    Some(self.builder.inst_results(call)[0])
                }
            }
            hir::Expr::Global(path) => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn {
                        module: self.fqn.module,
                        name,
                    },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let global_data = self.compile_global(fqn);

                let local_id = self
                    .module
                    .declare_data_in_func(global_data, self.builder.func);

                let pointer = self.module.target_config().pointer_type();
                let global_ptr = self.builder.ins().symbol_value(pointer, local_id);

                let global_ty = self.tys[fqn]
                    .as_global()
                    .unwrap()
                    .ty
                    .to_comp_type(self.module, self.resolved_arena);

                if global_ty.is_pointer_type() {
                    Some(global_ptr)
                } else {
                    Some(self.builder.ins().load(
                        global_ty.into_real_type().unwrap(),
                        MemFlags::new().with_aligned(),
                        global_ptr,
                        0,
                    ))
                }
            }
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.compile_stmt(&stmt);
                }

                if let Some(val) = tail_expr {
                    self.compile_expr_with_args(val, _no_deref)
                } else {
                    None
                }
            }
            hir::Expr::If {
                condition,
                body,
                else_branch,
            } => {
                let condition = self.compile_expr(condition).unwrap();

                // build branch
                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                let return_ty = self.tys[self.fqn.module][expr]
                    .to_comp_type(self.module, self.resolved_arena)
                    .into_real_type();

                if let Some(return_ty) = return_ty {
                    self.builder.append_block_param(merge_block, return_ty);
                }

                self.builder
                    .ins()
                    .brif(condition, then_block, &[], else_block, &[]);

                // build then block

                self.builder.switch_to_block(then_block);
                self.builder.seal_block(then_block);

                match self.compile_expr(body) {
                    Some(then_value) => {
                        self.builder.ins().jump(merge_block, &[then_value]);
                    }
                    None => {
                        self.builder.ins().jump(merge_block, &[]);
                    }
                }

                // build else block

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);

                match else_branch.and_then(|else_branch| self.compile_expr(else_branch)) {
                    Some(then_value) => {
                        self.builder.ins().jump(merge_block, &[then_value]);
                    }
                    None => {
                        self.builder.ins().jump(merge_block, &[]);
                    }
                }

                // build merge block

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                if return_ty.is_some() {
                    let phi = self.builder.block_params(merge_block)[0];

                    Some(phi)
                } else {
                    None
                }
            }
            hir::Expr::While { condition, body } => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.builder.ins().jump(header_block, &[]);
                self.builder.switch_to_block(header_block);

                if let Some(condition) =
                    condition.and_then(|condition| self.compile_expr(condition))
                {
                    self.builder
                        .ins()
                        .brif(condition, body_block, &[], exit_block, &[]);
                } else {
                    self.builder.ins().jump(body_block, &[]);
                }

                self.builder.switch_to_block(body_block);
                self.builder.seal_block(body_block);

                self.compile_expr(body);

                self.builder.ins().jump(header_block, &[]);

                // We've reached the bottom of the loop, so there will be no
                // more backedges to the header to exits to the bottom.
                self.builder.seal_block(header_block);

                self.builder.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);

                None
            }
            hir::Expr::Local(local_def) => self
                .locals
                .get(&local_def)
                .map(|var| self.builder.use_var(*var)),
            hir::Expr::Param { idx } => self
                .params
                .get(&(idx as u64))
                .map(|param| self.builder.use_var(*param)),
            hir::Expr::PrimitiveTy { .. } => None,
        }
    }
}

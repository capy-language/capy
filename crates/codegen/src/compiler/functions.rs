use std::{collections::VecDeque, str::FromStr};

use cranelift::{
    codegen::ir::{BlockArg, Endianness, FuncRef},
    frontend::Switch,
    prelude::{
        types, AbiParam, Block, FloatCC, FunctionBuilder, InstBuilder, IntCC, MemFlags,
        StackSlotData, StackSlotKind, TrapCode, Value, Variable,
    },
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use hir::{FQComptime, LocalDef, ScopeId, SwitchArg};
use hir_ty::{ComptimeResult, InternTyDisplay, InternTyExt, ParamTy, Ty};
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use uid_gen::UIDGenerator;

use crate::{
    builtin::{self, BuiltinFunction, BuiltinGlobal},
    convert::{GetFinalTy, ToTyId},
    debug::{write_nice_function, NiceFuncWriter},
    layout::{self, GetLayoutInfo},
    mangle::{self, Mangle},
    FinalSignature,
};

use super::{
    abi::{Abi, FnAbi},
    comptime::{ComptimeBytes, IntBytes},
    ComptimeData, FunctionToCompile, MemoryLoc, MetaTyData, MetaTyInfoArrays, MetaTyLayoutArrays,
};

struct UnfinishedComptimeErr;

/// represents a single block containing multiple defer statements
#[derive(Debug, Clone)]
pub(crate) struct DeferFrame {
    id: Option<ScopeId>,
    defers: Vec<Idx<hir::Expr>>,
}

/// todo: should this be a different number?
const TRAP_UNREACHABLE: TrapCode = TrapCode::unwrap_user(10);

/// Compiles a Capy function into a Cranelift function.
///
/// The main function to look at here is `compile_expr` or `compile_expr_with_args`
pub(crate) struct FunctionCompiler<'a> {
    pub(crate) final_binary: bool,

    pub(crate) file_name: hir::FileName,

    pub(crate) mod_dir: &'a std::path::Path,
    pub(crate) interner: &'a Interner,
    pub(crate) world_bodies: &'a hir::WorldBodies,
    pub(crate) tys: &'a hir_ty::ProjectInference,

    pub(crate) builder: FunctionBuilder<'a>,
    pub(crate) module: &'a mut dyn Module,
    pub(crate) data_description: &'a mut DataDescription,
    pub(crate) ptr_ty: types::Type,

    pub(crate) functions_to_compile: &'a mut VecDeque<FunctionToCompile>,
    pub(crate) meta_tys: &'a mut MetaTyData,
    pub(crate) cmd_args_slice: &'a mut Option<DataId>,

    pub(crate) local_functions: FxHashMap<hir::Fqn, FuncRef>,
    pub(crate) local_lambdas: FxHashMap<Idx<hir::Lambda>, FuncRef>,

    // globals
    pub(crate) functions: &'a mut FxHashMap<hir::Fqn, FuncId>,
    pub(crate) user_extern_functions: &'a mut FxHashMap<hir::Name, FuncId>,
    pub(crate) internal_extern_functions: &'a mut FxHashMap<&'static str, FuncId>,
    pub(crate) compiler_defined_functions: &'a mut FxHashMap<BuiltinFunction, FuncId>,
    pub(crate) globals: &'a mut FxHashMap<hir::Fqn, DataId>,
    pub(crate) str_id_gen: &'a mut UIDGenerator,
    pub(crate) i128_id_gen: &'a mut UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<FQComptime, ComptimeResult>,
    pub(crate) comptime_data: &'a mut FxHashMap<FQComptime, ComptimeData>,

    // variables
    pub(crate) locals: FxHashMap<Idx<LocalDef>, Value>,
    pub(crate) switch_locals: FxHashMap<Idx<SwitchArg>, Value>,
    pub(crate) params: FxHashMap<u64, Variable>,

    // for control flow (breaks and continues)
    pub(crate) exits: FxHashMap<ScopeId, Block>,
    pub(crate) continues: FxHashMap<ScopeId, Block>,
    pub(crate) defer_stack: Vec<DeferFrame>,

    // for prettier debugging
    pub(crate) func_writer: NiceFuncWriter,
}

impl FunctionCompiler<'_> {
    pub(crate) fn finish(
        mut self,
        fn_abi: FnAbi,
        (args, return_ty): (&Vec<ParamTy>, Intern<Ty>),
        function_body: Idx<hir::Expr>,
        debug_print: bool,
        mangled_name: &str,
    ) {
        fn_abi.build_fn(&mut self, return_ty, args, function_body);

        if debug_print {
            let mut buffer = String::new();
            write_nice_function(
                &mut self.func_writer,
                &mut buffer,
                self.builder.func,
                mangled_name,
            )
            .expect("there was an error printing the function");
            print!("{buffer}");
        }

        self.builder.finalize();
    }

    /// Returns `None` if any inner comptime blocks haven't been evaluated yet
    fn expr_to_const_data(
        &mut self,
        file_name: hir::FileName,
        expr: Idx<hir::Expr>,
    ) -> Result<Box<[u8]>, UnfinishedComptimeErr> {
        if let Some(meta_ty) = self.tys[file_name].get_meta_ty(expr)
            && *self.tys[file_name][expr] == Ty::Type
        {
            let id = meta_ty.to_type_id(self.meta_tys, self.ptr_ty);

            return Ok(match self.module.isa().endianness() {
                Endianness::Big => Box::new(id.to_be_bytes()),
                Endianness::Little => Box::new(id.to_le_bytes()),
            });
        }

        Ok(match self.world_bodies[file_name][expr].clone() {
            hir::Expr::Missing => unreachable!(),
            hir::Expr::IntLiteral(n) => {
                match (
                    self.tys[file_name][expr]
                        .get_final_ty()
                        .into_number_type()
                        .unwrap()
                        .bit_width(),
                    self.module.isa().endianness(),
                ) {
                    (8, Endianness::Little) => Box::new((n as u8).to_le_bytes()),
                    (8, Endianness::Big) => Box::new((n as u8).to_be_bytes()),
                    (16, Endianness::Little) => Box::new((n as u16).to_le_bytes()),
                    (16, Endianness::Big) => Box::new((n as u16).to_be_bytes()),
                    (32, Endianness::Little) => Box::new((n as u32).to_le_bytes()),
                    (32, Endianness::Big) => Box::new((n as u32).to_be_bytes()),
                    #[allow(clippy::unnecessary_cast)]
                    (64, Endianness::Little) => Box::new((n as u64).to_le_bytes()),
                    #[allow(clippy::unnecessary_cast)]
                    (64, Endianness::Big) => Box::new((n as u64).to_be_bytes()),
                    (128, Endianness::Little) => Box::new((n as u128).to_le_bytes()),
                    (128, Endianness::Big) => Box::new((n as u128).to_be_bytes()),
                    _ => unreachable!(),
                }
            }
            hir::Expr::FloatLiteral(f) => match (
                self.tys[file_name][expr]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap()
                    .bit_width(),
                self.module.isa().endianness(),
            ) {
                (32, Endianness::Little) => Box::new((f as f32).to_le_bytes()),
                (32, Endianness::Big) => Box::new((f as f32).to_be_bytes()),
                #[allow(clippy::unnecessary_cast)]
                (64, Endianness::Little) => Box::new((f as f64).to_le_bytes()),
                #[allow(clippy::unnecessary_cast)]
                (64, Endianness::Big) => Box::new((f as f64).to_be_bytes()),
                _ => unreachable!(),
            },
            hir::Expr::BoolLiteral(b) => Box::new([b as u8]),
            hir::Expr::StringLiteral(text) => {
                let text = self.interner.lookup(text);
                let mut s = String::with_capacity(text.len() + 1);
                s.push_str(text);
                s.push('\0');
                s.into_bytes().into()
            }
            hir::Expr::ArrayLiteral { items, .. } => {
                assert_ne!(items.len(), 0);

                let item_ty = self.tys[file_name][items[0]];
                let item_size = item_ty.size();
                let item_stride = item_ty.stride();

                let mut array = Vec::<u8>::with_capacity(item_stride as usize * items.len());

                for (idx, item) in items.into_iter().enumerate() {
                    let item = self.expr_to_const_data(file_name, item)?;

                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            item.as_ptr(),
                            array.as_mut_ptr().add(idx * item_stride as usize),
                            item_size as usize,
                        );
                    }
                }

                unsafe { array.set_len(array.capacity()) }

                array.into()
            }
            hir::Expr::Comptime(comptime) => {
                let ctc = FQComptime {
                    file: file_name,
                    expr,
                    comptime,
                };

                self.comptime_results
                    .get(&ctc)
                    .ok_or_else(|| {
                        if self.final_binary {
                            println!("{:#?}", self.comptime_results.keys().collect::<Vec<_>>());
                            println!(
                                "{} {:?}",
                                self.file_name.to_string(self.mod_dir, self.interner),
                                ctc
                            );
                            panic!("The final binary should not have uncompiled comptime blocks");
                        } else {
                            UnfinishedComptimeErr
                        }
                    })?
                    .clone()
                    .into_bytes(self.meta_tys, self.module.isa().endianness(), self.ptr_ty)
                    .unwrap()
            }
            hir::Expr::Local(local) => {
                let local_def = &self.world_bodies[file_name][local];

                assert!(
                    local_def.value.is_some(),
                    "if the value doesn't exist, `get_const` should've returned non-const, and there should be an error before codegen"
                );

                return self.expr_to_const_data(file_name, local_def.value.unwrap());
            }
            hir::Expr::LocalGlobal(global) => {
                let fqn = hir::Fqn {
                    file: file_name,
                    name: global.name,
                };

                return self.expr_to_const_data(file_name, self.world_bodies.body(fqn));
            }
            hir::Expr::Member {
                previous,
                name: field,
            } => {
                if let Ty::File(file) = self.tys[file_name][previous].as_ref() {
                    let fqn = hir::Fqn {
                        file: *file,
                        name: field.name,
                    };

                    return self.expr_to_const_data(fqn.file, self.world_bodies.body(fqn));
                } else {
                    panic!(
                        "constant members should only access files {} #{}",
                        file_name.to_string(self.mod_dir, self.interner),
                        expr.into_raw()
                    )
                }
            }
            _ => panic!(
                "tried to compile const with non-compilable definition {}#{}",
                file_name.to_string(self.mod_dir, self.interner),
                expr.into_raw()
            ),
        })
    }

    fn compile_global_binding_data(
        &mut self,
        fqn: hir::Fqn,
    ) -> Result<DataId, UnfinishedComptimeErr> {
        if let Some(global) = self.globals.get(&fqn) {
            return Ok(*global);
        }

        if self.world_bodies.is_extern(fqn) {
            let global = self
                .module
                .declare_data(
                    self.interner.lookup(fqn.name.0),
                    Linkage::Import,
                    true,
                    false,
                )
                .expect("error declaring data");

            self.globals.insert(fqn, global);

            return Ok(global);
        }

        let value = self.world_bodies.body(fqn);

        if let hir::Expr::Directive { name, args } = &self.world_bodies[fqn.file][value]
            && self.interner.lookup(name.name.0) == "builtin"
        {
            let builtin_name = args[0];
            let hir::Expr::StringLiteral(builtin_name) = &self.world_bodies[fqn.file][builtin_name]
            else {
                // todo: report an error
                unreachable!("an error should have been reported")
            };

            let builtin_kind =
                hir_ty::BuiltinKind::from_str(self.interner.lookup(*builtin_name)).unwrap();
            let builtin_global: BuiltinGlobal = builtin_kind.into();

            return Ok(self.compile_builtin_global(builtin_global));
        }

        let bytes = self.expr_to_const_data(fqn.file, value)?;

        let global = self.create_global_data(
            &fqn.to_mangled_name(self.mod_dir, self.interner),
            false,
            bytes,
            self.tys[fqn].0.align() as u64,
        );

        self.globals.insert(fqn, global);

        Ok(global)
    }

    fn create_global_data(
        &mut self,
        name: &str,
        export: bool,
        data: Box<[u8]>,
        align: u64,
    ) -> DataId {
        // todo: if the data isn't mutable, combine globals with identical definitions

        let id = self
            .module
            .declare_data(
                name,
                if export {
                    Linkage::Export
                } else {
                    Linkage::Local
                },
                false,
                false,
            )
            .expect("error declaring data");

        self.data_description.define(data);
        self.data_description.set_align(align);
        self.module
            .define_data(id, self.data_description)
            .expect("error defining data");
        self.data_description.clear();

        id
    }

    fn create_global_str(&mut self, mut text: String) -> DataId {
        text.push('\0');
        let name = format!(".str_{}", self.str_id_gen.generate_unique_id());
        self.create_global_data(&name, false, text.into_bytes().into_boxed_slice(), 1)
    }

    fn create_global_i128(&mut self, num: u64) -> DataId {
        let name = format!(".i128_{}", self.i128_id_gen.generate_unique_id());
        self.create_global_data(
            &name,
            false,
            num.into_bytes(self.module.isa().endianness(), 128)
                .into_boxed_slice(),
            1,
        )
    }

    #[allow(unused)]
    fn build_memcpy_ty(&mut self, src: Value, dest: Value, ty: Intern<Ty>, non_overlapping: bool) {
        self.builder.emit_small_memory_copy(
            self.module.target_config(),
            dest,
            src,
            ty.stride() as u64,
            ty.align() as u8,
            ty.align() as u8,
            non_overlapping,
            MemFlags::trusted(),
        )
    }

    fn get_func_id(&mut self, fqn: hir::Fqn) -> FuncId {
        super::get_func_id(
            self.module,
            self.ptr_ty,
            self.mod_dir,
            self.functions,
            self.user_extern_functions,
            self.internal_extern_functions,
            self.compiler_defined_functions,
            self.functions_to_compile,
            self.tys,
            self.world_bodies,
            self.interner,
            fqn,
        )
    }

    fn get_or_create_extern_func_id(
        &mut self,
        name: &'static str,
        params: Vec<AbiParam>,
        returns: Vec<AbiParam>,
    ) -> FuncId {
        if let Some(func_id) = self.internal_extern_functions.get(name).or_else(|| {
            self.interner
                .get_interned(name)
                .and_then(|key| self.user_extern_functions.get(&hir::Name(key)))
        }) {
            return *func_id;
        }

        let func_id = self
            .module
            .declare_function(
                name,
                Linkage::Import,
                &FinalSignature {
                    params,
                    returns,
                    call_conv: self.module.target_config().default_call_conv,
                },
            )
            .expect("There are multiple extern functions with the same name");

        self.internal_extern_functions.insert(name, func_id);

        func_id
    }

    fn get_local_func(&mut self, fqn: hir::Fqn) -> FuncRef {
        if let Some(func_ref) = self.local_functions.get(&fqn) {
            return *func_ref;
        }

        let func_id = self.get_func_id(fqn);

        let local_func = self.module.declare_func_in_func(func_id, self.builder.func);

        self.local_functions.insert(fqn, local_func);

        local_func
    }

    fn compile_global(&mut self, fqn: hir::Fqn, no_load: bool) -> Option<Value> {
        let ty = &self.tys[fqn].0;

        if ty.is_zero_sized() {
            return None;
        } else if ty.is_function() {
            let local_func = self.get_local_func(fqn);

            return Some(self.builder.ins().func_addr(self.ptr_ty, local_func));
        }

        let Ok(global_data) = self.compile_global_binding_data(fqn) else {
            // there was an unfinished comptime
            let body = self.world_bodies.body(fqn);

            // todo: could this cause issues?
            let old_file_name = std::mem::replace(&mut self.file_name, fqn.file);
            let res = self.compile_expr_with_args(body, no_load);
            self.file_name = old_file_name;

            return res;
        };

        let local_id = self
            .module
            .declare_data_in_func(global_data, self.builder.func);

        let global_ptr = self.builder.ins().symbol_value(self.ptr_ty, local_id);
        // TODO: find out the difference between symbol_value and global_value.
        // they both return pointers.

        let final_ty = ty.get_final_ty();

        if no_load || final_ty.is_pointer_type() {
            Some(global_ptr)
        } else {
            Some(self.builder.ins().load(
                final_ty.into_real_type().unwrap(),
                MemFlags::trusted(),
                global_ptr,
                0,
            ))
        }
    }

    fn compile_stmt(&mut self, stmt: &Idx<hir::Stmt>) {
        match self.world_bodies[self.file_name][*stmt] {
            hir::Stmt::Expr(expr) => {
                match *self.tys[self.file_name][expr] {
                    hir_ty::Ty::Unknown => unreachable!(),
                    _ => {
                        self.compile_expr(expr);
                    }
                };
            }
            hir::Stmt::LocalDef(local_def) => {
                let ty = self.tys[self.file_name][local_def];

                let value = self.world_bodies[self.file_name][local_def].value;

                let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: ty.size(),
                    align_shift: ty.align_shift(),
                });

                let memory = MemoryLoc::from_stack(stack_slot, 0);

                if let Some(value) = value {
                    // the type of the value might not be the same as the type annotation of the
                    // declaration
                    self.compile_and_cast_into_memory(value, ty, memory);
                } else {
                    self.store_default_in_memory(ty, memory);
                }

                self.locals
                    .insert(local_def, memory.into_value(&mut self.builder, self.ptr_ty));
            }
            hir::Stmt::Assign(assign) => {
                let assign_body = &self.world_bodies[self.file_name][assign];

                let Some(dest) = self.compile_expr_with_args(assign_body.dest, true) else {
                    return;
                };
                let dest = MemoryLoc::from_addr(dest, 0);

                let dest_ty = &self.tys[self.file_name][assign_body.dest];

                if let Some(op) = assign_body.quick_assign_op {
                    let res = self.compile_binary(assign_body.dest, assign_body.value, op);

                    assert!(!dest_ty.is_aggregate());

                    dest.write_all(res, *dest_ty, self.module, &mut self.builder);
                } else {
                    self.compile_and_cast_into_memory(assign_body.value, *dest_ty, dest);
                }
            }
            hir::Stmt::Break {
                label: Some(label),
                value,
                ..
            } => {
                let value = value.and_then(|value| {
                    let referenced_block_ty =
                        self.tys[self.file_name][self.world_bodies[self.file_name][label]];

                    self.compile_and_cast(value, referenced_block_ty)
                });

                self.break_to_label(value, label);
            }
            hir::Stmt::Break { label: None, .. } => unreachable!(),
            hir::Stmt::Continue {
                label: Some(label), ..
            } => {
                let continue_block = self.continues[&label];

                self.builder.ins().jump(continue_block, &[]);
            }
            hir::Stmt::Continue { label: None, .. } => unreachable!(),
            hir::Stmt::Defer { expr, .. } => {
                // defer statements aren't actually compiled here, but only at the end of blocks,
                // or during a break. We use stacks like this so breaks can execute all the defers
                // between their location and the desired location.

                self.defer_stack
                    .last_mut()
                    .expect("block didn't add to defer stack")
                    .defers
                    .push(expr);
            }
        }
    }

    /// This pushes a final jump instruction to the block, meaning additional operations
    /// won't be allowed in the current block
    fn break_to_label(&mut self, value: Option<Value>, label: hir::ScopeId) {
        let exit_block = self.exits[&label];

        // run all the defers from here, backwards to the one we are breaking out of

        let mut used_frames = Vec::new();

        // todo: don't do popping
        while let Some(frame) = self.defer_stack.last().cloned() {
            // the exit block of every Expr::Block contains the instructions for running
            // the defers. This break instruction jumps to that exit block.
            // therefore, we only need to insert extra defer handling for everything OTHER
            // than the block we are breaking to.
            if let Some(id) = frame.id {
                if id == label {
                    break;
                }
            }

            // do it in reverse to make sure later defers can still rely on the allocations of
            // previous defers
            for defer in frame.defers.iter().rev() {
                self.compile_expr(*defer);
            }

            used_frames.push(self.defer_stack.pop().unwrap());
        }

        self.defer_stack.extend(used_frames.into_iter().rev());

        if let Some(value) = value {
            self.builder
                .ins()
                .jump(exit_block, &[BlockArg::Value(value)]);
        } else {
            self.builder.ins().jump(exit_block, &[]);
        };
    }

    fn store_default_in_memory(&mut self, expected_ty: Intern<Ty>, memory: MemoryLoc) {
        let value = match expected_ty.as_ref() {
            Ty::NotYetResolved | Ty::Unknown => unreachable!(),
            Ty::IInt(_) | Ty::UInt(_) => {
                let number_ty = expected_ty.get_final_ty().into_number_type().unwrap();
                match number_ty.bit_width() {
                    128 => {
                        let data = self.create_global_i128(0);

                        let local_id = self.module.declare_data_in_func(data, self.builder.func);

                        let addr = self.builder.ins().symbol_value(self.ptr_ty, local_id);

                        self.builder
                            .ins()
                            .load(types::I128, MemFlags::trusted(), addr, 0)
                    }
                    _ => self.builder.ins().iconst(number_ty.ty, 0),
                }
            }
            Ty::Float(bit_width) => match bit_width {
                32 => self.builder.ins().f32const(0.0),
                64 => self.builder.ins().f64const(0.0),
                _ => unreachable!(),
            },
            Ty::Bool => self.builder.ins().iconst(types::I8, 0),
            Ty::String => unreachable!("str does not have a default value"),
            Ty::Char => self.builder.ins().iconst(types::I8, 0),
            Ty::AnonArray { size, sub_ty } | Ty::ConcreteArray { size, sub_ty, .. } => {
                let inner_stride = sub_ty.stride();

                for idx in 0..*size {
                    let byte_offset = idx as u32 * inner_stride;
                    self.store_default_in_memory(*sub_ty, memory.with_offset(byte_offset));
                }
                return;
            }
            Ty::Slice { .. } => unreachable!("slices do not have default values"),
            Ty::Pointer { .. } => unreachable!("pointers do not have default values"),
            Ty::Distinct { sub_ty, .. } => {
                self.store_default_in_memory(*sub_ty, memory);
                return;
            }
            Ty::Type => unreachable!("types do not have default values"),
            Ty::Any => unreachable!("any does not have a default value"),
            Ty::RawPtr { .. } => unreachable!("rawptr does not have a default value"),
            Ty::RawSlice => unreachable!("rawslice does not have a default value"),
            Ty::File(_) => unreachable!("files do not have default values"),
            Ty::Function { .. } => unreachable!("functions do not have default values"),
            Ty::AnonStruct { members } | Ty::ConcreteStruct { members, .. } => {
                let struct_mem = expected_ty.struct_layout().unwrap();

                for (idx, hir_ty::MemberTy { ty, .. }) in members.iter().enumerate() {
                    self.store_default_in_memory(
                        *ty,
                        memory.with_offset(struct_mem.offsets()[idx]),
                    );
                }
                return;
            }
            Ty::Enum { .. } => unreachable!("enums do not have default values"),
            Ty::EnumVariant { sub_ty, .. } => {
                self.store_default_in_memory(*sub_ty, memory);
                return;
            }
            Ty::Optional { .. } => {
                memory.memset(self.module, &mut self.builder, 0, expected_ty);
                return;
            }
            Ty::ErrorUnion { .. } => unreachable!("error unions do not have default values"),
            // void is just a no-op
            Ty::Void => return,
            // nil is just a no-op
            Ty::Nil => return,
            Ty::AlwaysJumps => return,
        };

        memory.write_val(&mut self.builder, value, 0);
    }

    fn store_expr_in_memory(
        &mut self,
        expr: Idx<hir::Expr>,
        expected_ty: Intern<Ty>,
        memory: MemoryLoc,
    ) {
        let expr_ty = self.tys[self.file_name][expr];

        // if the expression has to be casted in order to become the expected type, do that.
        // the one cast this applies to is `any` casting.
        if !expr_ty.is_functionally_equivalent_to(&expected_ty, true) {
            // todo: this could probably be made even more efficient
            self.compile_and_cast_into_memory(expr, expected_ty, memory);
            return;
        }

        match &self.world_bodies[self.file_name][expr] {
            hir::Expr::ArrayLiteral { items, .. } => {
                let (_, sub_ty) = expected_ty
                    .as_array()
                    .expect("array literals should have an array type");
                // fixed array
                self.store_array_items(items.iter().copied(), sub_ty, memory)
            }
            hir::Expr::StructLiteral {
                members: member_values,
                ..
            } => self.store_struct_fields(expected_ty, member_values, memory),
            _ => {
                let val = self.compile_expr(expr);

                memory.write_all(val, expected_ty, self.module, &mut self.builder);
            }
        }
    }

    fn store_struct_fields(
        &mut self,
        struct_ty: Intern<Ty>,
        field_values: &[hir::MemberLiteral],
        memory: MemoryLoc,
    ) {
        assert!(struct_ty.is_struct());

        let field_tys = struct_ty.as_struct().unwrap();
        let struct_mem = struct_ty.struct_layout().unwrap();

        for hir::MemberLiteral { name, value } in field_values {
            let field = field_tys
                .iter()
                .enumerate()
                .find(|(_, defined_field)| defined_field.name == name.unwrap().name)
                .unwrap();

            self.store_expr_in_memory(
                *value,
                field.1.ty,
                memory.with_offset(struct_mem.offsets()[field.0]),
            );
        }
    }

    fn store_array_items(
        &mut self,
        items: impl Iterator<Item = Idx<hir::Expr>>,
        // this has to be given since the items may autocast into the actual sub type
        sub_ty: Intern<Ty>,
        memory: MemoryLoc,
    ) {
        let stride = sub_ty.stride();

        for (idx, item) in items.enumerate() {
            let byte_offset = idx as u32 * stride;
            self.store_expr_in_memory(item, sub_ty, memory.with_offset(byte_offset))
        }
    }

    fn compile_expr(&mut self, expr: Idx<hir::Expr>) -> Option<Value> {
        self.compile_expr_with_args(expr, false)
    }

    /// `no_load` will cause the first encountered deref to not deref at all.
    /// this is used for assignment
    fn compile_expr_with_args(&mut self, expr: Idx<hir::Expr>, no_load: bool) -> Option<Value> {
        if let Some(meta_ty) = self.tys[self.file_name].get_meta_ty(expr)
            && *self.tys[self.file_name][expr] == Ty::Type
        {
            let id = meta_ty.to_type_id(self.meta_tys, self.ptr_ty);

            return Some(self.builder.ins().iconst(types::I32, id as i64));
        }

        match self.world_bodies[self.file_name][expr].clone() {
            hir::Expr::Missing => unreachable!(),
            hir::Expr::IntLiteral(n) => {
                let number_ty = self.tys[self.file_name][expr]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap();
                if number_ty.float {
                    match number_ty.bit_width() {
                        32 => Some(self.builder.ins().f32const(n as f32)),
                        64 => Some(self.builder.ins().f64const(n as f64)),
                        _ => unreachable!(),
                    }
                } else {
                    match number_ty.bit_width() {
                        128 => {
                            let data = self.create_global_i128(n);

                            let local_id =
                                self.module.declare_data_in_func(data, self.builder.func);

                            let addr = self.builder.ins().symbol_value(self.ptr_ty, local_id);

                            Some(
                                self.builder
                                    .ins()
                                    .load(types::I128, MemFlags::trusted(), addr, 0),
                            )
                        }
                        _ => Some(self.builder.ins().iconst(number_ty.ty, n as i64)),
                    }
                }
            }
            hir::Expr::FloatLiteral(f) => {
                match self.tys[self.file_name][expr]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap()
                    .bit_width()
                {
                    32 => Some(self.builder.ins().f32const(f as f32)),
                    64 => Some(self.builder.ins().f64const(f)),
                    _ => unreachable!(),
                }
            }
            hir::Expr::BoolLiteral(b) => Some(self.builder.ins().iconst(types::I8, b as i64)),
            hir::Expr::StringLiteral(text) => {
                let text = self.interner.lookup(text);
                let mut s = String::with_capacity(text.len() + 1);
                s.push_str(text);
                let data = self.create_global_str(s);

                let local_id = self.module.declare_data_in_func(data, self.builder.func);

                Some(self.builder.ins().symbol_value(self.ptr_ty, local_id))
            }
            hir::Expr::CharLiteral(char) => Some(self.builder.ins().iconst(types::I8, char as i64)),
            hir::Expr::ArrayDecl { .. } => None,
            hir::Expr::ArrayLiteral { items, .. } => {
                let ty = self.tys[self.file_name][expr];

                let (_, sub_ty) = ty.as_array().unwrap_or_else(|| {
                    panic!(
                        "{} #{} : array literal has type {ty:?} instead of an array type",
                        self.file_name.debug(self.interner),
                        expr.into_raw()
                    )
                });

                if ty.is_zero_sized() {
                    return None;
                }

                let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: ty.size(),
                    align_shift: ty.align_shift(),
                });

                let memory = MemoryLoc::from_stack(stack_slot, 0);

                self.store_array_items(items.iter().copied(), sub_ty, memory);

                Some(memory.into_value(&mut self.builder, self.ptr_ty))
            }
            hir::Expr::Index { source, index } => {
                if self.tys[self.file_name][expr].is_zero_sized() {
                    return None;
                }

                let mut source_ty = self.tys[self.file_name][source];
                let mut source = self.compile_expr(source).unwrap(); // this will be usize

                let mut required_derefs = 0;
                while let Some((_, sub_ty)) = source_ty.as_pointer() {
                    source_ty = sub_ty;
                    required_derefs += 1;
                }
                debug_assert!(source_ty.is_array() || source_ty.is_slice());

                for _ in 1..required_derefs {
                    source = self
                        .builder
                        .ins()
                        .load(self.ptr_ty, MemFlags::trusted(), source, 0);
                }

                let index_ty = self.tys[self.file_name][index];

                let index = self.compile_expr(index).unwrap();

                // make sure that the index is a usize before proceeding
                let naive_index =
                    super::cast_ty_to_cranelift(&mut self.builder, index, index_ty, self.ptr_ty);

                let (len, source) = if let Some((len, _)) = source_ty.as_array() {
                    (self.builder.ins().iconst(self.ptr_ty, len as i64), source)
                } else {
                    let len = self
                        .builder
                        .ins()
                        .load(self.ptr_ty, MemFlags::trusted(), source, 0);
                    let source = self.builder.ins().load(
                        self.ptr_ty,
                        MemFlags::trusted(),
                        source,
                        self.ptr_ty.bytes() as i32,
                    );

                    (len, source)
                };

                let is_good_index =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThan, naive_index, len);

                self.compile_unreachablez(
                    is_good_index,
                    Some(if source_ty.is_array() {
                        "array index out of bounds"
                    } else {
                        assert!(source_ty.is_slice());
                        "slice index out of bounds"
                    }),
                );

                // now we have to align the index, the elements of the array only start every
                // so many bytes (4 bytes for i32, 8 bytes for i64)
                // So the index has to be multiplied by the element stride
                let element_ty = self.tys[self.file_name][expr];

                let byte_offset = self
                    .builder
                    .ins()
                    .imul_imm(naive_index, element_ty.stride() as i64);

                let final_addr = self.builder.ins().iadd(source, byte_offset);

                if no_load || element_ty.is_aggregate() {
                    Some(final_addr)
                } else {
                    Some(self.builder.ins().load(
                        element_ty.get_final_ty().into_real_type().unwrap(),
                        MemFlags::new().with_aligned(),
                        final_addr,
                        0,
                    ))
                }
            }
            hir::Expr::Cast { expr: None, .. } => {
                self.cast(None, Ty::Void.into(), self.tys[self.file_name][expr])
            }
            hir::Expr::Cast {
                expr: Some(inner_expr),
                ..
            } => {
                let cast_to = self.tys[self.file_name][expr];

                self.compile_and_cast(inner_expr, cast_to)
            }
            hir::Expr::Ref { expr, .. } => {
                if self.tys[self.file_name][expr].is_aggregate()
                    || matches!(
                        self.world_bodies[self.file_name][expr],
                        hir::Expr::Local(_)
                            | hir::Expr::LocalGlobal(_)
                            | hir::Expr::Index { .. }
                            | hir::Expr::Member { .. }
                    )
                {
                    // references to locals or globals should return the actual memory address of the local or global
                    let res = self.compile_expr_with_args(expr, true);

                    if res.is_some() {
                        res
                    } else {
                        // even though the expression is void, we still need to get some
                        // result

                        let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                            kind: StackSlotKind::ExplicitSlot,
                            size: 0,
                            align_shift: 0, // 1 << 0 == 1
                        });

                        Some(self.builder.ins().stack_addr(self.ptr_ty, stack_slot, 0))
                    }
                } else {
                    let inner_ty = self.tys[self.file_name][expr];

                    // println!("{:?} = {inner_size}", self.tys[self.fqn.module][expr]);

                    let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                        kind: StackSlotKind::ExplicitSlot,
                        size: inner_ty.size(),
                        align_shift: inner_ty.align_shift(),
                    });

                    if let Some(expr) = self.compile_expr(expr) {
                        self.builder.ins().stack_store(expr, stack_slot, 0);
                    }

                    Some(self.builder.ins().stack_addr(self.ptr_ty, stack_slot, 0))
                }
            }
            hir::Expr::Deref { pointer } => {
                let self_ty = self.tys[self.file_name][expr];

                if self_ty.is_aggregate() {
                    return self.compile_expr_with_args(pointer, false);
                }

                let addr = self.compile_expr_with_args(pointer, false)?;

                let self_ty = self_ty.get_final_ty();

                let self_ty = if no_load {
                    self.ptr_ty
                } else {
                    self_ty.into_real_type().unwrap()
                };

                if no_load {
                    Some(addr)
                } else {
                    Some(
                        self.builder
                            .ins()
                            .load(self_ty, MemFlags::trusted(), addr, 0),
                    )
                }
            }
            hir::Expr::Binary {
                lhs: lhs_expr,
                rhs: rhs_expr,
                op,
            } => self.compile_binary(lhs_expr, rhs_expr, op),
            hir::Expr::Unary { expr: inner, op } => {
                let expr_ty = self.tys[self.file_name][inner]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap();

                let expr = self.compile_expr(inner).unwrap();

                if expr_ty.float {
                    match op {
                        hir::UnaryOp::Pos => Some(expr),
                        hir::UnaryOp::Neg => Some(self.builder.ins().fneg(expr)),
                        hir::UnaryOp::BNot => Some(self.builder.ins().bnot(expr)),
                        hir::UnaryOp::LNot => unreachable!(),
                    }
                } else {
                    match op {
                        hir::UnaryOp::Pos => Some(expr),
                        hir::UnaryOp::Neg => Some(self.builder.ins().ineg(expr)),
                        hir::UnaryOp::BNot => Some(self.builder.ins().bnot(expr)),
                        hir::UnaryOp::LNot => {
                            let zero = self.builder.ins().iconst(expr_ty.ty, 0);
                            Some(self.builder.ins().icmp(IntCC::Equal, expr, zero))
                        }
                    }
                }
            }
            hir::Expr::Call { callee, args } => {
                let (param_tys, return_ty) = self.tys[self.file_name][callee]
                    .clone()
                    .as_function()
                    .unwrap();
                let fn_abi = Into::<Abi>::into(self.module.target_config())
                    .fn_to_target((&param_tys, return_ty));

                // first, figure out how many varargs there are for each parameter
                let mut params_iter = param_tys.iter();
                let mut args_iter = args.iter();

                let mut current_param = params_iter.next();
                let mut current_arg = args_iter.next();

                #[derive(Debug, PartialEq, Eq)]
                struct ArgToCompile<'a> {
                    values: Vec<Idx<hir::Expr>>,
                    associated_param: &'a ParamTy,
                }

                let mut actual_args = Vec::with_capacity(args.len());
                let mut working_arg = None::<ArgToCompile>;
                loop {
                    let Some(arg) = current_arg else {
                        if let Some(param) = current_param {
                            // there are more params than args
                            if param.varargs {
                                // something has to be pushed.
                                // look at this example:
                                // ```
                                // core.println();
                                // ```
                                // what will happen here?
                                // if we push nothing, a slice won't be created.
                                // and if a slice isn't created, there will be an error, because
                                // the definition of `println` expects a slice.
                                if let Some(working_arg) = working_arg {
                                    actual_args.push(working_arg);
                                } else {
                                    actual_args.push(ArgToCompile {
                                        values: Vec::new(),
                                        associated_param: param,
                                    });
                                }
                                break; // break without reporting error
                            }

                            unreachable!("an error should have been reported");
                        }
                        if let Some(working_arg) = working_arg {
                            actual_args.push(working_arg);
                        }
                        break;
                    };
                    let arg_ty = self.tys[self.file_name][*arg];

                    let Some(param) = current_param else {
                        // there are more args than params
                        unreachable!("an error should have been reported");
                    };

                    if param.varargs {
                        let actual_sub_ty = param.ty.as_slice().unwrap();

                        if arg_ty.can_fit_into(&actual_sub_ty) {
                            let working = working_arg.get_or_insert_with(|| ArgToCompile {
                                values: Vec::with_capacity(1),
                                associated_param: param,
                            });

                            working.values.push(*arg);

                            current_arg = args_iter.next();
                        } else if let Some(next_param) = params_iter.next() {
                            // go to the next param but don't go to the next arg.
                            // this basically just reevaluates the current argument
                            // under the next parameter.
                            current_param = Some(next_param);
                            actual_args
                                .push(working_arg.take().expect("it should be Some(_) here"));
                        } else {
                            unreachable!("an error should have been reported");
                        }
                    } else {
                        assert_eq!(working_arg, None);

                        actual_args.push(ArgToCompile {
                            values: vec![*arg],
                            associated_param: param,
                        });

                        current_param = params_iter.next();
                        current_arg = args_iter.next();
                    }
                }

                // second, actually compile each argument and vararg
                let mut arg_values = Vec::with_capacity(args.len());
                for arg in actual_args {
                    if arg.associated_param.varargs {
                        let actual_sub_ty = arg.associated_param.ty.as_slice().unwrap();
                        let stride = actual_sub_ty.stride();

                        let array_stack_slot =
                            self.builder.create_sized_stack_slot(StackSlotData {
                                kind: StackSlotKind::ExplicitSlot,
                                size: stride * arg.values.len() as u32,
                                align_shift: actual_sub_ty.align_shift(),
                            });
                        let array_mem = MemoryLoc::from_stack(array_stack_slot, 0);

                        for (idx, value) in arg.values.iter().enumerate() {
                            self.compile_and_cast_into_memory(
                                *value,
                                actual_sub_ty,
                                array_mem.with_offset(idx as u32 * stride),
                            );
                        }

                        assert!(arg.associated_param.ty.is_slice());
                        let slice_stack_slot =
                            self.builder.create_sized_stack_slot(StackSlotData {
                                kind: StackSlotKind::ExplicitSlot,
                                size: arg.associated_param.ty.size(),
                                align_shift: arg.associated_param.ty.align_shift(),
                            });

                        let len_val = self
                            .builder
                            .ins()
                            .iconst(self.ptr_ty, arg.values.len() as i64);
                        self.builder.ins().stack_store(len_val, slice_stack_slot, 0);

                        let array_addr =
                            self.builder
                                .ins()
                                .stack_addr(self.ptr_ty, array_stack_slot, 0);
                        self.builder.ins().stack_store(
                            array_addr,
                            slice_stack_slot,
                            self.ptr_ty.bytes() as i32,
                        );

                        let slice_addr =
                            self.builder
                                .ins()
                                .stack_addr(self.ptr_ty, slice_stack_slot, 0);

                        arg_values.push(slice_addr);
                    } else {
                        assert_eq!(arg.values.len(), 1);

                        if let Some(value) =
                            self.compile_and_cast(arg.values[0], arg.associated_param.ty)
                        {
                            arg_values.push(value);
                        }
                    }
                }

                let mut arg_values = fn_abi.get_arg_list(arg_values, self);

                let ret_mem =
                    fn_abi.ret_addr(&mut arg_values, &mut self.builder, return_ty, self.ptr_ty);

                let call = match self.world_bodies[self.file_name][callee] {
                    hir::Expr::LocalGlobal(name) => {
                        let fqn = hir::Fqn {
                            file: self.file_name,
                            name: name.name,
                        };

                        let local_func = self.get_local_func(fqn);

                        self.builder.ins().call(local_func, &arg_values)
                    }
                    hir::Expr::Local(local)
                        if !self.world_bodies[self.file_name][local].mutable =>
                    {
                        let value = self.world_bodies[self.file_name][local].value;

                        if let Some(hir::Expr::Lambda(lambda)) =
                            value.map(|value| &self.world_bodies[self.file_name][value])
                        {
                            let local_func = self.unnamed_func_to_local(callee, *lambda);

                            self.builder.ins().call(local_func, &arg_values)
                        } else {
                            let callee = self.compile_expr(callee).unwrap();

                            let comp_sig = fn_abi
                                .to_cl(self.ptr_ty, self.module.target_config().default_call_conv);

                            let sig_ref = self.builder.import_signature(comp_sig);

                            self.builder
                                .ins()
                                .call_indirect(sig_ref, callee, &arg_values)
                        }
                    }
                    hir::Expr::Member {
                        previous,
                        name: field,
                        ..
                    } => match &self.tys[self.file_name][previous].as_ref() {
                        Ty::File(file) => {
                            let fqn = hir::Fqn {
                                file: *file,
                                name: field.name,
                            };

                            let local_func = self.get_local_func(fqn);

                            self.builder.ins().call(local_func, &arg_values)
                        }
                        _ => {
                            let callee = self.compile_expr(callee).unwrap();

                            let comp_sig = fn_abi
                                .to_cl(self.ptr_ty, self.module.target_config().default_call_conv);

                            let sig_ref = self.builder.import_signature(comp_sig);

                            self.builder
                                .ins()
                                .call_indirect(sig_ref, callee, &arg_values)
                        }
                    },
                    hir::Expr::Lambda(lambda) => {
                        let local_func = self.unnamed_func_to_local(callee, lambda);

                        self.builder.ins().call(local_func, &arg_values)
                    }
                    _ => {
                        let callee = self.compile_expr(callee).unwrap();

                        let comp_sig = fn_abi
                            .to_cl(self.ptr_ty, self.module.target_config().default_call_conv);
                        let sig_ref = self.builder.import_signature(comp_sig);

                        self.builder
                            .ins()
                            .call_indirect(sig_ref, callee, &arg_values)
                    }
                };

                if return_ty.is_zero_sized() {
                    None
                } else {
                    fn_abi.handle_ret(call, self, ret_mem)
                }
            }
            hir::Expr::Paren(Some(inner)) => self.compile_expr_with_args(inner, no_load),
            hir::Expr::Paren(None) => None,
            hir::Expr::Block { stmts, tail_expr } => {
                let expr_ty = self.tys[self.file_name][expr];
                let final_ty = expr_ty.get_final_ty();

                let body_block = self.builder.create_block();
                self.func_writer[body_block] = "block_body".into();
                let exit_block = self.builder.create_block();
                self.func_writer[exit_block] = "block_exit".into();
                if let Some(ty) = final_ty.into_real_type() {
                    self.builder.append_block_param(exit_block, ty);
                }
                let scope_id = self.world_bodies[self.file_name].block_to_scope_id(expr);
                if let Some(scope_id) = scope_id {
                    self.exits.insert(scope_id, exit_block);
                }

                self.defer_stack.push(DeferFrame {
                    id: scope_id,
                    defers: Vec::new(),
                });

                self.builder.ins().jump(body_block, &[]);

                self.builder.switch_to_block(body_block);
                self.builder.seal_block(body_block);

                let mut no_eval = false;
                for stmt in stmts {
                    self.compile_stmt(&stmt);
                    match self.world_bodies[self.file_name][stmt] {
                        // if the current scope id is `None`
                        // (no one breaks to the end of this block)
                        // AND a sub expression has the type `NoEval`
                        // (it always breaks, but not to the end of itself)
                        // then the sub expression must be breaking to a higher block
                        hir::Stmt::Expr(expr)
                            if scope_id.is_none()
                                && *self.tys[self.file_name][expr] == Ty::AlwaysJumps =>
                        {
                            no_eval = true;
                            break;
                        }
                        hir::Stmt::Break { .. } | hir::Stmt::Continue { .. } => {
                            no_eval = true;
                            break;
                        }
                        _ => {}
                    }
                }

                let value = (!no_eval)
                    .then(|| {
                        tail_expr.and_then(|tail_expr| {
                            let value =
                                self.compile_and_cast_with_args(tail_expr, no_load, expr_ty);
                            // unlike before, where we had to make sure the scope id is `None`,
                            // here, if the tail doesn't reach its own end (and it doesn't evaluate
                            // to anything) then *we* aren't going to evaluate to anything.
                            if *self.tys[self.file_name][tail_expr] == Ty::AlwaysJumps {
                                no_eval = true;
                            }
                            value
                        })
                    })
                    .flatten();

                if !no_eval {
                    if let Some(value) = value {
                        self.builder
                            .ins()
                            .jump(exit_block, &[BlockArg::Value(value)]);
                    } else if tail_expr.is_none() && !expr_ty.can_be_created_from_nothing() {
                        // we know this block somehow reaches it's end (because we already checked it's !no_eval)
                        //
                        // we also know it doesn't have a tail expression
                        //
                        // we also know it has a type which can't be created from nothing (no implicit tail expression)
                        //
                        // due to that fact, the type checker must have already confirmed that
                        // it *always* reaches a break. we can actually assert that.
                        //
                        // that's the only way a block like this can exist. If there was no break
                        // then there would've been an error and we wouldn't be doing codegen rn.
                        //
                        // the reason we check `tail_expr` and not `value` is because `value` might
                        // be something like `None` from a value of `nil` (a zero-sized type)
                        //
                        // the reason we need to trap is because cranelift forces us to end all blocks with
                        // a "final" instruction (a jump or trap). we can't exactly jump to the exit
                        // because we don't have a value with which to jump (and recall that the exit
                        // is expecting something which can't be created from nothing).
                        //
                        // So, since it's safe to trap, we just trap.
                        assert!(scope_id.is_some());
                        self.compile_unreachable(Some("end of noreturn block reached"));
                    } else {
                        // note that we still might get zero-sized types here in this branch that *can't* be
                        // created from nothing because they made the value `None`

                        if expr_ty.is_zero_sized() {
                            self.builder.ins().jump(exit_block, &[]);
                        } else {
                            assert!(
                                expr_ty.can_be_created_from_nothing(),
                                "{expr_ty:?} can't be created from nothing"
                            );

                            // This might be because of something like this:
                            //
                            // ```
                            // my_block : ?void = {
                            //      core.println("hello");
                            // };
                            // ```
                            //
                            // `?void` can be created from nothing (it can be created from a void)
                            // but it itself actually does have a size.
                            //
                            // So here we create a value from nothing.
                            //
                            // TODO: what if this `.into()` screws things up in a program where
                            // `Ty::Void` has never been created?
                            let something = self
                                .cast(None, Ty::Void.into(), expr_ty)
                                .expect("we already checked for zero-sized types");

                            self.builder
                                .ins()
                                .jump(exit_block, &[BlockArg::Value(something)]);
                        }
                    }
                }

                self.builder.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);

                // unwind our defers

                let defer_frame = self.defer_stack.pop().expect("we just pushed this");

                if !no_eval || scope_id.is_some() {
                    debug_assert_eq!(defer_frame.id, scope_id);

                    // do it in reverse to make sure later defers can still rely on the allocations of
                    // previous defers
                    for defer in defer_frame.defers.iter().rev() {
                        self.compile_expr(*defer);
                    }
                }

                if final_ty.into_real_type().is_some() {
                    Some(self.builder.block_params(exit_block)[0])
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

                let then_block = self.builder.create_block();
                self.func_writer[then_block] = "if_then".into();
                let else_block = self.builder.create_block();
                self.func_writer[else_block] = "if_else".into();
                let merge_block = self.builder.create_block();
                self.func_writer[merge_block] = "if_exit".into();

                let return_ty = self.tys[self.file_name][expr];
                let return_ty_real = return_ty.get_final_ty().into_real_type();

                if let Some(return_ty) = return_ty_real {
                    self.builder.append_block_param(merge_block, return_ty);
                }

                self.builder
                    .ins()
                    .brif(condition, then_block, &[], else_block, &[]);

                // build then block

                self.builder.switch_to_block(then_block);
                self.builder.seal_block(then_block);

                let body_value = self.compile_and_cast_with_args(body, no_load, return_ty);

                if *self.tys[self.file_name][body] == Ty::AlwaysJumps {
                    self.compile_unreachable(Some("end of noreturn then block reached"));
                } else {
                    match body_value {
                        Some(then_value) => {
                            self.builder
                                .ins()
                                .jump(merge_block, &[BlockArg::Value(then_value)]);
                        }
                        None => {
                            self.builder.ins().jump(merge_block, &[]);
                        }
                    }
                }

                // build else block

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);

                if let Some(else_branch) = else_branch {
                    let else_value =
                        self.compile_and_cast_with_args(else_branch, no_load, return_ty);

                    if *self.tys[self.file_name][else_branch] == Ty::AlwaysJumps {
                        self.compile_unreachable(Some("end of noreturn else block reached"));
                    } else {
                        match else_value {
                            Some(then_value) => {
                                self.builder
                                    .ins()
                                    .jump(merge_block, &[BlockArg::Value(then_value)]);
                            }
                            None => {
                                self.builder.ins().jump(merge_block, &[]);
                            }
                        }
                    }
                } else {
                    self.builder.ins().jump(merge_block, &[]);
                }

                // build merge block

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                if return_ty_real.is_some() {
                    let phi = self.builder.block_params(merge_block)[0];

                    Some(phi)
                } else {
                    None
                }
            }
            hir::Expr::While { condition, body } => {
                let header_block = self.builder.create_block();
                self.func_writer[header_block] = "while_header".into();
                let body_block = self.builder.create_block();
                self.func_writer[body_block] = "while_body".into();
                let exit_block = self.builder.create_block();
                self.func_writer[exit_block] = "while_exit".into();

                let ty = self.tys[self.file_name][expr].get_final_ty();

                if let Some(ty) = ty.into_real_type() {
                    self.builder.append_block_param(exit_block, ty);
                }
                if let Some(scope_id) = self.world_bodies[self.file_name].block_to_scope_id(expr) {
                    self.continues.insert(scope_id, header_block);
                    self.exits.insert(scope_id, exit_block);
                }

                self.builder.ins().jump(header_block, &[]);
                self.builder.switch_to_block(header_block);
                // don't seal the header yet

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
                // more jumps to the header
                self.builder.seal_block(header_block);

                self.builder.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);

                if ty.into_real_type().is_some() {
                    Some(self.builder.block_params(exit_block)[0])
                } else {
                    None
                }
            }
            hir::Expr::Switch {
                scrutinee,
                arms,
                default,
                ..
            } => {
                let sum_ty = self.tys[self.file_name][scrutinee];

                let arm_blocks: Vec<_> = arms
                    .iter()
                    .map(|arm| {
                        let arm_ty = match arm.variant.expect("should be Some") {
                            hir::ArmVariant::FullyQualified(ty) => {
                                self.tys[self.file_name].get_meta_ty(ty).unwrap()
                            }
                            hir::ArmVariant::Shorthand(name) => {
                                let Ty::Enum { ref variants, .. } = *sum_ty else {
                                    unreachable!()
                                };

                                variants
                                    .iter()
                                    .find(|v| {
                                        let Ty::EnumVariant { variant_name, .. } = ***v else {
                                            unreachable!()
                                        };

                                        variant_name == name.name
                                    })
                                    .copied()
                                    .unwrap()
                            }
                        };

                        // the name of the block is set later
                        (arm_ty, self.builder.create_block(), *arm)
                    })
                    .collect();

                let exit_block = self.builder.create_block();
                self.func_writer[exit_block] = "switch_exit".into();

                let return_ty = self.tys[self.file_name][expr];
                let return_ty_real = return_ty.get_final_ty().into_real_type();

                if let Some(ty) = return_ty_real {
                    self.builder.append_block_param(exit_block, ty);
                }

                let scrutinee_val = self
                    .compile_expr(scrutinee)
                    .expect("enums are never zero sized");

                if let Some(enum_layout) = sum_ty.enum_layout() {
                    assert!(sum_ty.is_tagged_union());

                    let default_block = self.builder.create_block();
                    self.func_writer[default_block] = "switch_default".into();

                    let discrim_val = self.builder.ins().load(
                        types::I8,
                        MemFlags::trusted(),
                        scrutinee_val,
                        enum_layout.discriminant_offset() as i32,
                    );

                    let mut switch = Switch::new();
                    for (variant_ty, arm_block, _) in &arm_blocks {
                        let discrim = sum_ty.get_tagged_union_discrim(variant_ty).unwrap();

                        // todo: maybe discriminant should also be u128
                        switch.set_entry(discrim as u128, *arm_block);
                        self.func_writer[*arm_block] =
                            format!("switch_arm_discrim{discrim}").into();
                    }

                    switch.emit(&mut self.builder, discrim_val, default_block);

                    self.builder.switch_to_block(default_block);
                    self.builder.seal_block(default_block);

                    if let Some(default) = default {
                        if let Some(switch_arg) = default.switch_arg {
                            self.switch_locals.insert(switch_arg, scrutinee_val);
                        }

                        // todo: should no_load be used here?
                        let default_val =
                            self.compile_and_cast_with_args(default.body, no_load, return_ty);

                        if let Some(default_val) = default_val {
                            self.builder
                                .ins()
                                .jump(exit_block, &[BlockArg::Value(default_val)]);
                        } else {
                            self.builder.ins().jump(exit_block, &[]);
                        }
                    } else {
                        self.compile_unreachable(Some("every branch of `switch` was missed"));
                    }
                } else {
                    // todo: include more tests for this
                    assert!(sum_ty.is_optional() && !sum_ty.is_tagged_union());
                    // the scrutinee should be a pointer
                    assert_eq!(self.builder.func.dfg.value_type(scrutinee_val), self.ptr_ty);
                    // todo: add support for default blocks here
                    assert!(default.is_none());

                    let is_some = self
                        .builder
                        .ins()
                        .icmp_imm(IntCC::NotEqual, scrutinee_val, 0);

                    assert_eq!(arm_blocks.len(), 2);
                    let (nil_idx, nil_block) = arm_blocks
                        .iter()
                        .enumerate()
                        .find(|(_, (ty, _, _))| **ty == Ty::Nil)
                        .expect("this is an optional");
                    assert!(nil_idx == 0 || nil_idx == 1);
                    let some_idx = (nil_idx == 0) as usize;
                    assert!(some_idx == 0 || some_idx == 1);
                    assert_ne!(some_idx, nil_idx);
                    let some_block = arm_blocks[some_idx];

                    self.func_writer[some_block.1] = "switch_arm_discrim1".into();
                    self.func_writer[nil_block.1] = "switch_arm_discrim0".into();

                    self.builder
                        .ins()
                        .brif(is_some, some_block.1, &[], nil_block.1, &[]);
                }

                for (variant_ty, arm_block, arm) in arm_blocks {
                    self.builder.switch_to_block(arm_block);
                    self.builder.seal_block(arm_block);

                    if let Some(switch_local) = arm.switch_arg
                        && let Some(inner_val) = super::unwrap_sum_ty(
                            &mut self.builder,
                            scrutinee_val,
                            sum_ty,
                            variant_ty,
                        )
                    {
                        self.switch_locals.insert(switch_local, inner_val);
                    }

                    let body_val = self.compile_and_cast_with_args(arm.body, no_load, return_ty);

                    if let Some(body_val) = body_val {
                        self.builder
                            .ins()
                            .jump(exit_block, &[BlockArg::Value(body_val)]);
                    } else {
                        self.builder.ins().jump(exit_block, &[]);
                    }
                }

                self.builder.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);

                if return_ty_real.is_some() {
                    Some(self.builder.block_params(exit_block)[0])
                } else {
                    None
                }
            }
            hir::Expr::Local(local_def) => {
                let ptr = *self.locals.get(&local_def)?;

                let ty = &self.tys[self.file_name][local_def];

                if no_load || ty.is_aggregate() {
                    Some(ptr)
                } else {
                    let ty = ty.get_final_ty();

                    // if it isn't a real type, this will just return None
                    ty.into_real_type()
                        .map(|ty| self.builder.ins().load(ty, MemFlags::trusted(), ptr, 0))
                }
            }
            hir::Expr::SwitchArgument(switch_local) => {
                self.switch_locals.get(&switch_local).copied()
            }
            hir::Expr::Param { idx, .. } => self
                .params
                .get(&(idx as u64))
                .map(|param| self.builder.use_var(*param)),
            hir::Expr::LocalGlobal(name) => {
                if self.tys[self.file_name][expr].is_zero_sized() {
                    return None;
                }

                let fqn = hir::Fqn {
                    file: self.file_name,
                    name: name.name,
                };

                self.compile_global(fqn, no_load)
            }
            hir::Expr::Member { previous, name, .. } => {
                if self.tys[self.file_name][expr].is_zero_sized() {
                    return None;
                }

                let previous_ty = self.tys[self.file_name][previous];
                match previous_ty.as_ref() {
                    Ty::File(file) => {
                        let fqn = hir::Fqn {
                            file: *file,
                            name: name.name,
                        };

                        self.compile_global(fqn, no_load)
                    }
                    _ => {
                        let field_ty = &self.tys[self.file_name][expr];
                        let field_comp_ty = field_ty.get_final_ty().into_real_type()?;

                        let mut required_derefs = 0;
                        let mut source_ty = previous_ty;
                        while let Some((_, sub_ty)) = source_ty.as_pointer() {
                            source_ty = sub_ty;
                            required_derefs += 1;
                        }
                        source_ty = source_ty.absolute_intern_ty(true);

                        match source_ty.as_ref() {
                            Ty::Slice { .. } | Ty::RawSlice => {
                                let slice = self.compile_expr(previous).unwrap();
                                let addr = match self.interner.lookup(name.name.0) {
                                    "len" => slice,
                                    "ptr" => self
                                        .builder
                                        .ins()
                                        .iadd_imm(slice, self.ptr_ty.bytes() as i64),
                                    _ => unreachable!(),
                                };
                                if no_load {
                                    return Some(addr);
                                } else {
                                    return Some(self.builder.ins().load(
                                        self.ptr_ty,
                                        MemFlags::trusted(),
                                        addr,
                                        0,
                                    ));
                                }
                            }
                            Ty::AnonArray { size, .. } | Ty::ConcreteArray { size, .. } => {
                                // the len isn't actually located anywhere in memory. In memory the
                                // array is just the raw data only. However, when you usually get the
                                // address of a field it returns the actual address of that field in
                                // the struct or slice, so here we have to fake it by allocating
                                // enough extra space on the stack for the len if we need to.
                                if no_load {
                                    let ss = self.builder.create_sized_stack_slot(StackSlotData {
                                        kind: StackSlotKind::ExplicitSlot,
                                        size: self.ptr_ty.bytes(),
                                        // todo: maybe do this better
                                        align_shift: self.ptr_ty.bytes().trailing_zeros() as u8,
                                    });

                                    let size = self.builder.ins().iconst(self.ptr_ty, *size as i64);
                                    self.builder.ins().stack_store(size, ss, 0);

                                    return Some(self.builder.ins().stack_addr(self.ptr_ty, ss, 0));
                                } else {
                                    return Some(
                                        self.builder.ins().iconst(self.ptr_ty, *size as i64),
                                    );
                                }
                            }
                            Ty::Any => {
                                let any = self.compile_expr(previous).unwrap();
                                let (addr, ty) = match self.interner.lookup(name.name.0) {
                                    "ty" => (any, types::I32),
                                    "ptr" => {
                                        let typeid_size = 32 / 8;

                                        let rawptr_size = self.ptr_ty.bytes();
                                        let rawptr_align = rawptr_size.min(8);
                                        let rawptr_offset = typeid_size
                                            + layout::padding_needed_for(typeid_size, rawptr_align);

                                        let addr =
                                            self.builder.ins().iadd_imm(any, rawptr_offset as i64);

                                        (addr, self.ptr_ty)
                                    }
                                    _ => unreachable!(),
                                };
                                if no_load {
                                    return Some(addr);
                                } else {
                                    return Some(self.builder.ins().load(
                                        ty,
                                        MemFlags::trusted(),
                                        addr,
                                        0,
                                    ));
                                }
                            }
                            _ => {}
                        }

                        let struct_fields = source_ty.as_struct().unwrap();

                        let field_idx = struct_fields
                            .iter()
                            .enumerate()
                            .find(|(_, source_member)| source_member.name == name.name)
                            .map(|(idx, _)| idx)
                            .unwrap();

                        let offset = source_ty.struct_layout().unwrap().offsets()[field_idx];

                        let mut struct_addr = self.compile_expr_with_args(previous, false)?;

                        for _ in 1..required_derefs {
                            struct_addr = self.builder.ins().load(
                                self.ptr_ty,
                                MemFlags::trusted(),
                                struct_addr,
                                0,
                            );
                        }

                        if no_load || field_ty.is_aggregate() {
                            Some(self.builder.ins().iadd_imm(struct_addr, offset as i64))
                        } else {
                            Some(self.builder.ins().load(
                                field_comp_ty,
                                MemFlags::trusted(),
                                struct_addr,
                                offset as i32,
                            ))
                        }
                    }
                }
            }
            hir::Expr::Lambda(lambda) => {
                let local_func = self.unnamed_func_to_local(expr, lambda);

                Some(self.builder.ins().func_addr(self.ptr_ty, local_func))
            }
            hir::Expr::StructLiteral {
                members: field_values,
                ..
            } => {
                let ty = self.tys[self.file_name][expr];

                let stack_slot = self.builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: ty.size(),
                    align_shift: ty.align_shift(),
                });

                let memory = MemoryLoc::from_stack(stack_slot, 0);

                self.store_struct_fields(ty, &field_values, memory);

                Some(memory.into_value(&mut self.builder, self.ptr_ty))
            }
            hir::Expr::PrimitiveTy { .. } => None,
            hir::Expr::Distinct { .. } => None,
            hir::Expr::StructDecl { .. } => None,
            hir::Expr::EnumDecl { .. } => None,
            // hir::Expr::Nil => {
            //     let opt_ty = self.tys[self.file_name][expr];
            //
            //     // if `sub_ty` is `None`, its a zero sized type and we can just return
            //
            //     self.create_nil_value(opt_ty)
            // }
            hir::Expr::Nil => None,
            hir::Expr::OptionalDecl { .. } => None,
            hir::Expr::ErrorUnionDecl { .. } => None,
            hir::Expr::Propagate { label: None, .. } => {
                unreachable!("`hir_ty` should've reported this")
            }
            hir::Expr::Propagate {
                label: Some(label),
                expr: inner,
                ..
            } => {
                let union = self.compile_expr(inner)?;
                let union_ty = self.tys[self.file_name][inner];
                assert!(matches!(
                    *union_ty,
                    Ty::Optional { .. } | Ty::ErrorUnion { .. }
                ));

                let payload_ty = self.tys[self.file_name][expr];

                let is_ok = if union_ty.is_error_union() {
                    super::tagged_union_has_discriminant(&mut self.builder, union_ty, union, 1)
                } else {
                    assert!(union_ty.is_optional());
                    super::optional_is_some(&mut self.builder, union_ty, union)
                };

                let err_block = self.builder.create_block();
                self.func_writer[err_block] = "propagate_error".into();
                let ok_block = self.builder.create_block();
                self.func_writer[ok_block] = "propagate_okay".into();

                self.builder
                    .ins()
                    .brif(is_ok, ok_block, &[], err_block, &[]);
                self.builder.seal_block(ok_block);
                self.builder.seal_block(err_block);

                self.builder.switch_to_block(err_block);

                let referenced_block_ty =
                    self.tys[self.file_name][self.world_bodies[self.file_name][label]];

                // if this try is propagating to a block who only ever resolves to `nil`, `void`, etc.
                // then we don't actually have to construct anything.
                if referenced_block_ty.is_zero_sized() {
                    if union_ty.is_optional() {
                        assert_eq!(
                            union_ty.propagated_ty().map(|ty| ty.as_ref()),
                            Some(&Ty::Nil)
                        );
                    }

                    self.break_to_label(None, label);
                } else if union_ty.is_optional() {
                    assert!(referenced_block_ty.is_optional());
                    let nil_value = super::create_nil_value(
                        &mut self.builder,
                        self.ptr_ty,
                        referenced_block_ty,
                        None,
                    );
                    self.break_to_label(Some(nil_value), label);
                } else if let Ty::ErrorUnion { error_ty, .. } = union_ty.absolute_ty() {
                    assert!(
                        referenced_block_ty
                            .propagated_ty()
                            .is_some_and(|ty| error_ty.can_cast_to(&ty))
                            || (!referenced_block_ty.is_error_union()
                                && error_ty.can_fit_into(&referenced_block_ty))
                    );

                    let error = super::unwrap_sum_ty(&mut self.builder, union, union_ty, *error_ty);

                    // this will construct a new error union with the error inside it
                    let casted = self.cast(error, *error_ty, referenced_block_ty);
                    self.break_to_label(casted, label);
                }

                self.builder.switch_to_block(ok_block);

                super::unwrap_sum_ty(&mut self.builder, union, union_ty, payload_ty)
            }
            hir::Expr::Import(_) => None,
            hir::Expr::Directive { name, args } => match self.interner.lookup(name.name.0) {
                "unwrap" => {
                    let sum_val = self
                        .compile_expr(args[0])
                        .expect("sum types are never zero-sized");
                    let sum_ty = self.tys[self.file_name][args[0]];
                    assert!(sum_ty.is_sum_ty(), "{sum_ty:?} is not a sum type");

                    let variant_ty = self.tys[self.file_name][expr];
                    assert!(
                        sum_ty.has_sum_variant(&variant_ty),
                        "{variant_ty:?} is not a variant of {sum_ty:?}"
                    );

                    if let Some(desired_discrim) = sum_ty.get_tagged_union_discrim(&variant_ty) {
                        let enum_layout = sum_ty.enum_layout().unwrap_or_else(|| {
                            panic!("{} #{} : the tagged union discriminant of {:?} is {} but there is no enum layout", self.file_name.debug(self.interner), args[0].into_raw(), sum_ty, desired_discrim)
                        });

                        let discrim = self.builder.ins().load(
                            types::I8,
                            MemFlags::trusted(),
                            sum_val,
                            enum_layout.discriminant_offset() as i32,
                        );

                        let is_correct_discrim = self.builder.ins().icmp_imm(
                            IntCC::Equal,
                            discrim,
                            desired_discrim as i64,
                        );

                        self.compile_unreachablez(
                            is_correct_discrim,
                            Some(&format!(
                                "called #unwrap({}, {}) but the variant was different",
                                sum_ty.named_display(self.mod_dir, self.interner, false),
                                variant_ty.named_display(self.mod_dir, self.interner, false)
                            )),
                        );

                        super::unwrap_sum_ty(&mut self.builder, sum_val, sum_ty, variant_ty)
                    } else {
                        assert!(sum_ty.is_optional());
                        assert!(!sum_ty.is_tagged_union());
                        // if aggregate non-zero types are added, we have to do a memcmp
                        assert!(!sum_ty.is_aggregate());

                        let is_correct_discrim = if *variant_ty == Ty::Nil {
                            self.builder.ins().icmp_imm(IntCC::Equal, sum_val, 0)
                        } else {
                            self.builder.ins().icmp_imm(IntCC::NotEqual, sum_val, 0)
                        };

                        self.compile_unreachablez(
                            is_correct_discrim,
                            Some(&format!(
                                "called #unwrap({}, {}) but the variant was different",
                                sum_ty.named_display(self.mod_dir, self.interner, false),
                                variant_ty.named_display(self.mod_dir, self.interner, false)
                            )),
                        );

                        super::unwrap_sum_ty(&mut self.builder, sum_val, sum_ty, variant_ty)
                    }
                }
                "is_variant" => {
                    let sum_val = self
                        .compile_expr(args[0])
                        .expect("sum types are never zero-sized");
                    let sum_ty = self.tys[self.file_name][args[0]];
                    assert!(sum_ty.is_sum_ty(), "{sum_ty:?} is not a sum type");

                    let variant_ty = self.tys[self.file_name].get_meta_ty(args[1]).unwrap();
                    assert!(
                        sum_ty.has_sum_variant(&variant_ty),
                        "{variant_ty:?} is not a variant of {sum_ty:?}"
                    );

                    if let Some(desired_discrim) = sum_ty.get_tagged_union_discrim(&variant_ty) {
                        let enum_layout = sum_ty.enum_layout().unwrap();

                        let discrim = self.builder.ins().load(
                            types::I8,
                            MemFlags::trusted(),
                            sum_val,
                            enum_layout.discriminant_offset() as i32,
                        );

                        let is_correct_discrim = self.builder.ins().icmp_imm(
                            IntCC::Equal,
                            discrim,
                            desired_discrim as i64,
                        );

                        Some(is_correct_discrim)
                    } else {
                        assert!(sum_ty.is_optional());
                        assert!(!sum_ty.is_tagged_union());
                        // if aggregate non-zero types are added, we have to do a memcmp
                        assert!(!sum_ty.is_aggregate());

                        if *variant_ty == Ty::Nil {
                            let is_none = self.builder.ins().icmp_imm(IntCC::Equal, sum_val, 0);

                            Some(is_none)
                        } else {
                            assert!(variant_ty.is_non_zero());
                            assert!(variant_ty.is_pointer());

                            let is_some = self.builder.ins().icmp_imm(IntCC::NotEqual, sum_val, 0);

                            Some(is_some)
                        }
                    }
                }
                _ => unreachable!(),
            },
            hir::Expr::Comptime(comptime) => {
                let ctc = FQComptime {
                    file: self.file_name,
                    expr,
                    comptime,
                };

                let ty = self.tys[self.file_name][expr];
                let final_ty = ty.get_final_ty();

                // if the comptime block was evaluated in a previous compilation step, then get that value.
                // otherwise, we are *in* the comptime eval step of compilation, and so create the instructions
                // neccessary to calculate the value of the comptime.
                if let Some(result) = self.comptime_results.get(&ctc) {
                    match result {
                        ComptimeResult::Type(ty) => {
                            Some(self.builder.ins().iconst(
                                types::I32,
                                ty.to_type_id(self.meta_tys, self.ptr_ty) as i64,
                            ))
                        }
                        ComptimeResult::Integer { num, .. } => Some(
                            self.builder
                                .ins()
                                .iconst(final_ty.into_real_type().unwrap(), *num as i64),
                        ),
                        ComptimeResult::Float { num, .. } => {
                            match final_ty.into_number_type().unwrap().bit_width() {
                                32 => Some(self.builder.ins().f32const(*num as f32)),
                                64 => Some(self.builder.ins().f64const(*num)),
                                _ => unreachable!(),
                            }
                        }
                        ComptimeResult::Data(bytes) => {
                            let data = self.create_global_data(
                                &ctc.to_mangled_name(self.mod_dir, self.interner),
                                false,
                                bytes.clone(),
                                ty.align() as u64,
                            );

                            let local_id =
                                self.module.declare_data_in_func(data, self.builder.func);

                            let global_ptr = self.builder.ins().symbol_value(self.ptr_ty, local_id);

                            if no_load || final_ty.is_pointer_type() {
                                Some(global_ptr)
                            } else {
                                Some(self.builder.ins().load(
                                    final_ty.into_real_type().unwrap(),
                                    MemFlags::trusted(),
                                    global_ptr,
                                    0,
                                ))
                            }
                        }
                        ComptimeResult::Void => None,
                    }
                } else {
                    let global = self.comptime_data.entry(ctc).or_insert_with(|| {
                        let data = ComptimeData::new(self.module, self.mod_dir, self.interner, ctc);

                        self.data_description.define_zeroinit(1);
                        self.module
                            .define_data(data.init_flag, self.data_description)
                            .expect("error defining data");
                        self.data_description.clear();

                        self.data_description.define_zeroinit(ty.size() as usize);
                        self.module
                            .define_data(data.value, self.data_description)
                            .expect("error defining data");
                        self.data_description.clear();

                        data
                    });

                    let init_flag_ptr = self
                        .module
                        .declare_data_in_func(global.init_flag, self.builder.func);
                    let init_flag_ptr = self.builder.ins().symbol_value(self.ptr_ty, init_flag_ptr);

                    let value_ptr = self
                        .module
                        .declare_data_in_func(global.value, self.builder.func);
                    let value_ptr = self.builder.ins().symbol_value(self.ptr_ty, value_ptr);

                    let init_flag =
                        self.builder
                            .ins()
                            .load(types::I8, MemFlags::trusted(), init_flag_ptr, 0);

                    let previous_block = self.builder.create_block();
                    self.func_writer[previous_block] = "comptime_get_previous".into();
                    let compute_block = self.builder.create_block();
                    self.func_writer[compute_block] = "comptime_compute".into();
                    let exit_block = self.builder.create_block();
                    self.func_writer[exit_block] = "comptime_exit".into();

                    self.builder
                        .ins()
                        .brif(init_flag, previous_block, &[], compute_block, &[]);

                    self.builder.switch_to_block(previous_block);
                    self.builder.seal_block(previous_block);

                    if let Some(real_ty) = final_ty.into_real_type() {
                        let value = if ty.is_aggregate() {
                            value_ptr
                        } else {
                            self.builder
                                .ins()
                                .load(real_ty, MemFlags::trusted(), value_ptr, 0)
                        };

                        self.builder
                            .ins()
                            .jump(exit_block, &[BlockArg::Value(value)]);
                    } else {
                        self.builder.ins().jump(exit_block, &[]);
                    }

                    self.builder.switch_to_block(compute_block);
                    self.builder.seal_block(compute_block);
                    self.builder.set_cold_block(compute_block);

                    self.store_expr_in_memory(
                        self.world_bodies[self.file_name][comptime].body,
                        ty,
                        MemoryLoc::from_addr(value_ptr, 0),
                    );

                    let true_val = self.builder.ins().iconst(types::I8, 1);
                    self.builder
                        .ins()
                        .store(MemFlags::trusted(), true_val, init_flag_ptr, 0);

                    if let Some(real_ty) = final_ty.into_real_type() {
                        let value = if ty.is_aggregate() {
                            value_ptr
                        } else {
                            self.builder
                                .ins()
                                .load(real_ty, MemFlags::trusted(), value_ptr, 0)
                        };

                        self.builder
                            .ins()
                            .jump(exit_block, &[BlockArg::Value(value)]);
                    } else {
                        self.builder.ins().jump(exit_block, &[]);
                    }

                    self.builder.switch_to_block(exit_block);
                    self.builder.seal_block(exit_block);

                    if let Some(ty) = final_ty.into_real_type() {
                        self.builder.append_block_param(exit_block, ty);
                        Some(self.builder.block_params(exit_block)[0])
                    } else {
                        None
                    }
                }
            }
        }
    }

    fn compile_binary(
        &mut self,
        lhs_expr: Idx<hir::Expr>,
        rhs_expr: Idx<hir::Expr>,
        op: hir::BinaryOp,
    ) -> Option<Value> {
        let lhs = |comp: &mut Self| comp.compile_expr(lhs_expr).unwrap();
        let rhs = |comp: &mut Self| comp.compile_expr(rhs_expr).unwrap();

        match op {
            hir::BinaryOp::LAnd => return Some(self.logical_and(lhs, rhs)),
            hir::BinaryOp::LOr => return Some(self.logical_or(lhs, rhs)),
            _ => {}
        }

        let lhs_ty = self.tys[self.file_name][lhs_expr];
        let rhs_ty = self.tys[self.file_name][rhs_expr];
        let max_ty: Intern<Ty> = lhs_ty
            .max(&rhs_ty)
            .expect("hir_ty would've caught this")
            .into();

        // zero-sized types are always equal
        if max_ty.is_zero_sized() {
            // We call compile_expr just so side-effects will occur.
            // The data gets thrown out anyway.
            assert_eq!(self.compile_expr(lhs_expr), None);
            assert_eq!(self.compile_expr(rhs_expr), None);

            match op {
                hir::BinaryOp::Eq => return Some(self.builder.ins().iconst(types::I8, 1)),
                hir::BinaryOp::Ne => return Some(self.builder.ins().iconst(types::I8, 0)),
                _ => unreachable!(),
            }
        }

        // Note that if an optional on the lhs is compared to a nil on the rhs, the rhs will be
        // zero-sized despite the fact that they will both get casted to a common maximum.

        let lhs = self.compile_and_cast(lhs_expr, max_ty).unwrap_or_else(|| {
            panic!(
                "{} #{} : LHS IS NONE ({lhs_ty:?}) {op:?} #{} ({rhs_ty:?})",
                self.file_name.debug(self.interner),
                lhs_expr.into_raw(),
                rhs_expr.into_raw()
            );
        });
        let rhs = self.compile_and_cast(rhs_expr, max_ty).unwrap_or_else(|| {
            panic!(
                "{} #{} : RHS IS NONE ({lhs_ty:?}) {op:?} #{} ({rhs_ty:?})",
                self.file_name.debug(self.interner),
                lhs_expr.into_raw(),
                rhs_expr.into_raw()
            );
        });

        Some(self.compile_complex_compare(lhs, rhs, max_ty, op))
    }

    fn compile_complex_compare(
        &mut self,
        lhs: Value,
        rhs: Value,
        ty: Intern<Ty>,
        hir_op: hir::BinaryOp,
    ) -> Value {
        assert!(!ty.is_zero_sized());

        if ty.get_final_ty().is_number_type() {
            return self.compile_num_binary(lhs, rhs, ty, hir_op);
        }

        let op = match hir_op {
            hir::BinaryOp::Eq => IntCC::Equal,
            hir::BinaryOp::Ne => IntCC::NotEqual,
            _ => unreachable!(),
        };

        match ty.absolute_ty() {
            Ty::NotYetResolved => unreachable!(),
            Ty::Unknown => unreachable!(),
            Ty::IInt(_) => unreachable!("already covered by `compile_num_binary`"),
            Ty::UInt(_) => unreachable!("already covered by `compile_num_binary`"),
            Ty::Float(_) => unreachable!("already covered by `compile_num_binary`"),
            Ty::Bool => unreachable!("already covered by `compile_num_binary`"),
            Ty::String => {
                // todo: when there are separate cstring and string types, keep this code for
                // cstring
                // todo: it's kind of hard for me to visualize this but I think there should be a
                // branchless way to do the inner logic

                let stage1 = self.builder.create_block();
                let stage1_lhs_addr = self.builder.append_block_param(stage1, self.ptr_ty);
                let stage1_rhs_addr = self.builder.append_block_param(stage1, self.ptr_ty);
                self.func_writer[stage1] = "string_cmp_stage1".into();
                let stage2 = self.builder.create_block();
                let stage2_lhs_addr = self.builder.append_block_param(stage2, self.ptr_ty);
                let stage2_rhs_addr = self.builder.append_block_param(stage2, self.ptr_ty);
                self.func_writer[stage2] = "string_cmp_stage2".into();
                let exit = self.builder.create_block();
                let exit_res = self.builder.append_block_param(exit, types::I8);
                self.func_writer[exit] = "string_cmp_exit".into();

                self.builder
                    .ins()
                    .jump(stage1, &[BlockArg::Value(lhs), BlockArg::Value(rhs)]);

                self.builder.switch_to_block(stage1);

                let lhs_byte =
                    self.builder
                        .ins()
                        .load(types::I8, MemFlags::trusted(), stage1_lhs_addr, 0);
                let rhs_byte =
                    self.builder
                        .ins()
                        .load(types::I8, MemFlags::trusted(), stage1_rhs_addr, 0);

                let same_bytes = self.builder.ins().icmp(op, lhs_byte, rhs_byte);

                match hir_op {
                    hir::BinaryOp::Eq => {
                        let r#false = self.builder.ins().iconst(types::I8, 0);
                        self.builder.ins().brif(
                            same_bytes,
                            stage2,
                            &[
                                BlockArg::Value(stage1_lhs_addr),
                                BlockArg::Value(stage1_rhs_addr),
                            ],
                            exit,
                            &[BlockArg::Value(r#false)],
                        );
                    }
                    hir::BinaryOp::Ne => {
                        let r#true = self.builder.ins().iconst(types::I8, 1);
                        self.builder.ins().brif(
                            same_bytes,
                            exit,
                            &[BlockArg::Value(r#true)],
                            stage2,
                            &[
                                BlockArg::Value(stage1_lhs_addr),
                                BlockArg::Value(stage1_rhs_addr),
                            ],
                        );
                    }
                    _ => unreachable!(),
                }

                self.builder.switch_to_block(stage2);
                self.builder.seal_block(stage2);

                let null_term = self.builder.ins().icmp_imm(IntCC::Equal, lhs_byte, 0);

                let next_lhs = self.builder.ins().iadd_imm(stage2_lhs_addr, 1);
                let next_rhs = self.builder.ins().iadd_imm(stage2_rhs_addr, 1);

                let true_val = self.builder.ins().iconst(types::I8, 1);
                let false_val = self.builder.ins().iconst(types::I8, 0);
                self.builder.ins().brif(
                    null_term,
                    exit,
                    &[match hir_op {
                        hir::BinaryOp::Eq => BlockArg::Value(true_val),
                        hir::BinaryOp::Ne => BlockArg::Value(false_val),
                        _ => unreachable!(),
                    }],
                    stage1,
                    &[BlockArg::Value(next_lhs), BlockArg::Value(next_rhs)],
                );

                self.builder.switch_to_block(exit);
                self.builder.seal_block(exit);
                self.builder.seal_block(stage1);

                exit_res
            }
            Ty::Char => unreachable!("already covered by `compile_num_binary`"),
            Ty::AnonArray { size, sub_ty } | Ty::ConcreteArray { size, sub_ty, .. } => {
                let size = self.builder.ins().iconst(self.ptr_ty, *size as i64);
                self.compile_array_compare(lhs, rhs, *sub_ty, size, hir_op)
            }
            Ty::Slice { sub_ty } => {
                // the len field is at offset 0
                let lhs_len = self
                    .builder
                    .ins()
                    .load(self.ptr_ty, MemFlags::trusted(), lhs, 0);
                let rhs_len = self
                    .builder
                    .ins()
                    .load(self.ptr_ty, MemFlags::trusted(), rhs, 0);

                // the array field is at offset size_of(usize)
                let lhs_data = self.builder.ins().load(
                    self.ptr_ty,
                    MemFlags::trusted(),
                    lhs,
                    self.ptr_ty.bytes() as i32,
                );
                let rhs_data = self.builder.ins().load(
                    self.ptr_ty,
                    MemFlags::trusted(),
                    rhs,
                    self.ptr_ty.bytes() as i32,
                );

                match hir_op {
                    hir::BinaryOp::Eq => self.logical_and(
                        |comp| comp.builder.ins().icmp(op, lhs_len, rhs_len),
                        |comp| {
                            comp.compile_array_compare(lhs_data, rhs_data, *sub_ty, lhs_len, hir_op)
                        },
                    ),
                    hir::BinaryOp::Ne => self.logical_or(
                        |comp| comp.builder.ins().icmp(op, lhs_len, rhs_len),
                        |comp| {
                            comp.compile_array_compare(lhs_data, rhs_data, *sub_ty, lhs_len, hir_op)
                        },
                    ),
                    _ => unreachable!(),
                }
            }
            Ty::Pointer { sub_ty, .. } => {
                let r#false = self.builder.ins().iconst(types::I8, 0);
                let r#true = self.builder.ins().iconst(types::I8, 1);

                // zero-sized types are always equal
                let Some(final_ty) = sub_ty.get_final_ty().into_real_type() else {
                    match hir_op {
                        hir::BinaryOp::Eq => return r#true,
                        hir::BinaryOp::Ne => return r#false,
                        _ => unreachable!(),
                    }
                };

                let lhs = self
                    .builder
                    .ins()
                    .load(final_ty, MemFlags::trusted(), lhs, 0);
                let rhs = self
                    .builder
                    .ins()
                    .load(final_ty, MemFlags::trusted(), rhs, 0);

                self.compile_complex_compare(lhs, rhs, *sub_ty, hir_op)
            }
            Ty::Distinct { .. } => unreachable!("called `absolute_ty`"),
            Ty::Type => unreachable!("already covered by `compile_num_binary`"),
            Ty::Any => unreachable!("any cannot be compared"),
            Ty::RawPtr { .. } => unreachable!("rawptr cannot be compared"),
            Ty::RawSlice => unreachable!("rawslice cannot be compared"),
            Ty::File(_) => unreachable!("files don't have a common max"),
            Ty::Function { .. } => unreachable!("functions don't have a common max"),
            Ty::AnonStruct { members } | Ty::ConcreteStruct { members, .. } => {
                let exit = self.builder.create_block();
                let exit_res = self.builder.append_block_param(exit, types::I8);
                self.func_writer[exit] = "array_cmp_exit".into();

                let struct_layout = ty.struct_layout().unwrap();

                let test_block = self.builder.create_block();
                self.func_writer[test_block] = "array_cmp_idx0".into();
                self.builder.ins().jump(test_block, &[]);
                self.builder.switch_to_block(test_block);
                self.builder.seal_block(test_block);

                for (idx, member) in members.iter().enumerate() {
                    let offset = struct_layout.offsets()[idx];

                    let lhs_addr = self.builder.ins().iadd_imm(lhs, offset as i64);
                    let rhs_addr = self.builder.ins().iadd_imm(rhs, offset as i64);
                    let res = if member.ty.is_aggregate() {
                        self.compile_complex_compare(lhs_addr, rhs_addr, member.ty, hir_op)
                    } else if let Some(real_ty) = member.ty.get_final_ty().into_real_type() {
                        let lhs_item =
                            self.builder
                                .ins()
                                .load(real_ty, MemFlags::trusted(), lhs_addr, 0);
                        let rhs_item =
                            self.builder
                                .ins()
                                .load(real_ty, MemFlags::trusted(), rhs_addr, 0);

                        self.compile_complex_compare(lhs_item, rhs_item, member.ty, hir_op)
                    } else {
                        assert!(member.ty.is_zero_sized());
                        unreachable!("shouldn't have gotten this far");
                    };

                    if idx < members.len() - 1 {
                        let next_test_block = self.builder.create_block();
                        self.func_writer[next_test_block] =
                            format!("array_cmp_next_idx{}", idx + 1).into();

                        match hir_op {
                            hir::BinaryOp::Eq => {
                                let false_val = self.builder.ins().iconst(types::I8, 0);
                                self.builder.ins().brif(
                                    res,
                                    next_test_block,
                                    &[],
                                    exit,
                                    &[BlockArg::Value(false_val)],
                                );
                            }
                            hir::BinaryOp::Ne => {
                                let true_val = self.builder.ins().iconst(types::I8, 1);
                                self.builder.ins().brif(
                                    res,
                                    exit,
                                    &[BlockArg::Value(true_val)],
                                    next_test_block,
                                    &[],
                                );
                            }
                            _ => unreachable!(),
                        };

                        self.builder.switch_to_block(next_test_block);
                        self.builder.seal_block(next_test_block);
                    } else {
                        self.builder.ins().jump(exit, &[BlockArg::Value(res)]);
                    }
                }

                self.builder.switch_to_block(exit);
                self.builder.seal_block(exit);

                exit_res
            }
            Ty::Enum { variants, .. } => self.compile_enum_compare(
                lhs,
                rhs,
                ty,
                variants.iter().map(|ty| {
                    let Ty::EnumVariant { discriminant, .. } = &**ty else {
                        unreachable!("only variants within enums");
                    };

                    (*discriminant as u128, Some(*ty))
                }),
                hir_op,
            ),
            Ty::EnumVariant { .. } => unreachable!("called `absolute_ty`"),
            Ty::Nil => unreachable!("tested for zero-sized types"),
            Ty::Optional { sub_ty } => {
                if sub_ty.is_non_zero() {
                    assert!(!ty.is_aggregate());

                    self.builder.ins().icmp(op, lhs, rhs)
                } else {
                    self.compile_enum_compare(
                        lhs,
                        rhs,
                        ty,
                        vec![(0, None), (1, Some(*sub_ty))].into_iter(),
                        hir_op,
                    )
                }
            }
            Ty::ErrorUnion {
                error_ty,
                payload_ty,
            } => self.compile_enum_compare(
                lhs,
                rhs,
                ty,
                vec![(0, Some(*error_ty)), (1, Some(*payload_ty))].into_iter(),
                hir_op,
            ),
            Ty::Void => unreachable!("tested for zero-sized types"),
            Ty::AlwaysJumps => unreachable!("tested for zero-sized types"),
        }
    }

    fn compile_enum_compare(
        &mut self,
        lhs: Value,
        rhs: Value,
        ty: Intern<Ty>,
        variants: impl Iterator<Item = (u128, Option<Intern<Ty>>)>,
        hir_op: hir::BinaryOp,
    ) -> Value {
        assert!(ty.is_tagged_union(), "{ty:?} is not a tagged union");

        let op = match hir_op {
            hir::BinaryOp::Eq => IntCC::Equal,
            hir::BinaryOp::Ne => IntCC::NotEqual,
            _ => unreachable!(),
        };

        let enum_layout = ty.enum_layout().unwrap();
        let lhs_discrim = self.builder.ins().load(
            types::I8,
            MemFlags::trusted(),
            lhs,
            enum_layout.discriminant_offset() as i32,
        );
        let rhs_discrim = self.builder.ins().load(
            types::I8,
            MemFlags::trusted(),
            rhs,
            enum_layout.discriminant_offset() as i32,
        );

        let arm_blocks: Vec<_> = variants
            .map(|(discrim, ty)| {
                let block = self.builder.create_block();
                self.func_writer[block] = format!("enum_cmp_arm_discrim{discrim}").into();
                (discrim, ty, block)
            })
            .collect();

        self.logical(
            hir_op,
            |comp| comp.builder.ins().icmp(op, lhs_discrim, rhs_discrim),
            |comp| {
                let exit = comp.builder.create_block();
                let exit_res = comp.builder.append_block_param(exit, types::I8);
                comp.func_writer[exit] = "enum_cmp_exit".into();

                let mut switch = Switch::new();
                for (discriminant, _, arm) in &arm_blocks {
                    switch.set_entry(*discriminant, *arm);
                }

                let default = comp.builder.create_block();
                comp.func_writer[default] = "enum_cmp_default".into();

                switch.emit(&mut comp.builder, lhs_discrim, default);

                comp.builder.switch_to_block(default);
                let true_val = comp.builder.ins().iconst(types::I8, 1);
                let false_val = comp.builder.ins().iconst(types::I8, 0);
                comp.builder.ins().jump(
                    exit,
                    &[match hir_op {
                        hir::BinaryOp::Eq => BlockArg::Value(true_val),
                        hir::BinaryOp::Ne => BlockArg::Value(false_val),
                        _ => unreachable!(),
                    }],
                );

                for (_, variant_ty, arm_block) in &arm_blocks {
                    comp.builder.switch_to_block(*arm_block);
                    comp.builder.seal_block(*arm_block);

                    if let Some(variant_ty) = *variant_ty {
                        // the payload begins at offset 0, so we can just use the lhs and rhs
                        // directly.
                        let res = if variant_ty.is_aggregate() {
                            comp.compile_complex_compare(lhs, rhs, variant_ty, hir_op)
                        } else if let Some(real_ty) = variant_ty.get_final_ty().into_real_type() {
                            let lhs_item =
                                comp.builder
                                    .ins()
                                    .load(real_ty, MemFlags::trusted(), lhs, 0);
                            let rhs_item =
                                comp.builder
                                    .ins()
                                    .load(real_ty, MemFlags::trusted(), rhs, 0);

                            comp.compile_complex_compare(lhs_item, rhs_item, variant_ty, hir_op)
                        } else {
                            assert!(variant_ty.is_zero_sized());

                            // zero-sized types are always equal
                            match hir_op {
                                hir::BinaryOp::Eq => comp.builder.ins().iconst(types::I8, 1),
                                hir::BinaryOp::Ne => comp.builder.ins().iconst(types::I8, 0),
                                _ => unreachable!(),
                            }
                        };

                        comp.builder.ins().jump(exit, &[BlockArg::Value(res)]);
                    } else {
                        comp.builder.ins().jump(default, &[]);
                    }
                }

                comp.builder.switch_to_block(exit);
                comp.builder.seal_block(exit);
                comp.builder.seal_block(default);

                exit_res
            },
        )
    }

    // todo: make sure this works for not equal
    fn compile_array_compare(
        &mut self,
        lhs: Value,
        rhs: Value,
        sub_ty: Intern<Ty>,
        size: Value,
        hir_op: hir::BinaryOp,
    ) -> Value {
        let false_val = self.builder.ins().iconst(types::I8, 0);
        let true_val = self.builder.ins().iconst(types::I8, 1);

        // zero-sized types are always equal
        if sub_ty.is_zero_sized() {
            match hir_op {
                hir::BinaryOp::Eq => return true_val,
                hir::BinaryOp::Ne => return false_val,
                _ => unimplemented!(),
            }
        }

        let idx = self.builder.declare_var(self.ptr_ty);
        let zero = self.builder.ins().iconst(self.ptr_ty, 0);
        self.builder.def_var(idx, zero);

        let header = self.builder.create_block();
        let header_idx = self.builder.append_block_param(header, self.ptr_ty);
        self.func_writer[header] = "array_cmp_header".into();
        let body = self.builder.create_block();
        let body_idx = self.builder.append_block_param(body, self.ptr_ty);
        self.func_writer[body] = "array_cmp_body".into();
        let exit = self.builder.create_block();
        let exit_bool = self.builder.append_block_param(exit, types::I8);
        self.func_writer[exit] = "array_cmp_exit".into();

        self.builder.ins().jump(header, &[BlockArg::Value(zero)]);

        self.builder.switch_to_block(header);
        let cond = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, header_idx, size);
        self.builder.ins().brif(
            cond,
            body,
            &[BlockArg::Value(header_idx)],
            exit,
            &[match hir_op {
                hir::BinaryOp::Eq => BlockArg::Value(true_val),
                hir::BinaryOp::Ne => BlockArg::Value(false_val),
                _ => unimplemented!(),
            }],
        );

        self.builder.switch_to_block(body);
        self.builder.seal_block(body);
        let offset = self
            .builder
            .ins()
            .imul_imm(body_idx, sub_ty.stride() as i64);
        let lhs_addr = self.builder.ins().iadd(lhs, offset);
        let rhs_addr = self.builder.ins().iadd(rhs, offset);
        let res = if sub_ty.is_aggregate() {
            self.compile_complex_compare(lhs_addr, rhs_addr, sub_ty, hir_op)
        } else if let Some(real_ty) = sub_ty.get_final_ty().into_real_type() {
            let lhs_item = self
                .builder
                .ins()
                .load(real_ty, MemFlags::trusted(), lhs_addr, 0);
            let rhs_item = self
                .builder
                .ins()
                .load(real_ty, MemFlags::trusted(), rhs_addr, 0);

            self.compile_complex_compare(lhs_item, rhs_item, sub_ty, hir_op)
        } else {
            assert!(sub_ty.is_zero_sized());
            unreachable!("shouldn't have gotten this far");
        };

        let idx_plus_one = self.builder.ins().iadd_imm(body_idx, 1);

        // if the check was successful, check the next item of the array, otherwise exit
        // with false

        match hir_op {
            hir::BinaryOp::Eq => {
                self.builder.ins().brif(
                    res,
                    header,
                    &[BlockArg::Value(idx_plus_one)],
                    exit,
                    &[BlockArg::Value(false_val)],
                );
            }
            hir::BinaryOp::Ne => {
                self.builder.ins().brif(
                    res,
                    exit,
                    &[BlockArg::Value(true_val)],
                    header,
                    &[BlockArg::Value(idx_plus_one)],
                );
            }
            _ => unimplemented!(),
        }

        self.builder.switch_to_block(exit);
        self.builder.seal_block(header);
        self.builder.seal_block(exit);

        exit_bool
    }

    fn compile_num_binary(
        &mut self,
        lhs: Value,
        rhs: Value,
        ty: Intern<Ty>,
        op: hir::BinaryOp,
    ) -> Value {
        let ty = ty.get_final_ty().into_number_type().unwrap();

        if ty.float {
            match op {
                hir::BinaryOp::Add => self.builder.ins().fadd(lhs, rhs),
                hir::BinaryOp::Sub => self.builder.ins().fsub(lhs, rhs),
                hir::BinaryOp::Mul => self.builder.ins().fmul(lhs, rhs),
                hir::BinaryOp::Div => self.builder.ins().fdiv(lhs, rhs),
                hir::BinaryOp::Mod => unreachable!(),
                hir::BinaryOp::Lt => self.builder.ins().fcmp(FloatCC::LessThan, lhs, rhs),
                hir::BinaryOp::Gt => self.builder.ins().fcmp(FloatCC::GreaterThan, lhs, rhs),
                hir::BinaryOp::Le => self.builder.ins().fcmp(FloatCC::LessThanOrEqual, lhs, rhs),
                hir::BinaryOp::Ge => self
                    .builder
                    .ins()
                    .fcmp(FloatCC::GreaterThanOrEqual, lhs, rhs),
                hir::BinaryOp::Eq => self.builder.ins().fcmp(FloatCC::Equal, lhs, rhs),
                hir::BinaryOp::Ne => self.builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs),
                hir::BinaryOp::BAnd => self.builder.ins().band(lhs, rhs),
                hir::BinaryOp::BOr => self.builder.ins().bor(lhs, rhs),
                hir::BinaryOp::Xor => self.builder.ins().bxor(lhs, rhs),
                hir::BinaryOp::LShift | hir::BinaryOp::RShift => unreachable!(),
                hir::BinaryOp::LAnd | hir::BinaryOp::LOr => unreachable!(),
            }
        } else {
            match op {
                hir::BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
                hir::BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
                hir::BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
                hir::BinaryOp::Div => {
                    if ty.signed {
                        self.builder.ins().sdiv(lhs, rhs)
                    } else {
                        self.builder.ins().udiv(lhs, rhs)
                    }
                }
                hir::BinaryOp::Mod => {
                    if ty.signed {
                        self.builder.ins().srem(lhs, rhs)
                    } else {
                        self.builder.ins().urem(lhs, rhs)
                    }
                }
                hir::BinaryOp::Lt => {
                    if ty.signed {
                        self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs)
                    } else {
                        self.builder.ins().icmp(IntCC::UnsignedLessThan, lhs, rhs)
                    }
                }
                hir::BinaryOp::Gt => {
                    if ty.signed {
                        self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs)
                    } else {
                        self.builder
                            .ins()
                            .icmp(IntCC::UnsignedGreaterThan, lhs, rhs)
                    }
                }
                hir::BinaryOp::Le => {
                    if ty.signed {
                        self.builder
                            .ins()
                            .icmp(IntCC::SignedLessThanOrEqual, lhs, rhs)
                    } else {
                        self.builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThanOrEqual, lhs, rhs)
                    }
                }
                hir::BinaryOp::Ge => {
                    if ty.signed {
                        self.builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs)
                    } else {
                        self.builder
                            .ins()
                            .icmp(IntCC::UnsignedGreaterThanOrEqual, lhs, rhs)
                    }
                }
                hir::BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, lhs, rhs),
                hir::BinaryOp::Ne => self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs),
                hir::BinaryOp::BAnd => self.builder.ins().band(lhs, rhs),
                hir::BinaryOp::BOr => self.builder.ins().bor(lhs, rhs),
                hir::BinaryOp::Xor => self.builder.ins().bxor(lhs, rhs),
                hir::BinaryOp::LShift => self.builder.ins().ishl(lhs, rhs),
                hir::BinaryOp::RShift => {
                    if ty.signed {
                        self.builder.ins().sshr(lhs, rhs)
                    } else {
                        self.builder.ins().ushr(lhs, rhs)
                    }
                }
                hir::BinaryOp::LAnd | hir::BinaryOp::LOr => unreachable!(),
            }
        }
    }

    // uses `logical_and` for Eq and `logical_or` for Ne
    fn logical(
        &mut self,
        op: hir::BinaryOp,
        lhs: impl Fn(&mut Self) -> Value,
        rhs: impl Fn(&mut Self) -> Value,
    ) -> Value {
        match op {
            hir::BinaryOp::Eq => self.logical_and(lhs, rhs),
            hir::BinaryOp::Ne => self.logical_or(lhs, rhs),
            _ => unreachable!(),
        }
    }

    fn logical_and(
        &mut self,
        lhs: impl FnOnce(&mut Self) -> Value,
        rhs: impl FnOnce(&mut Self) -> Value,
    ) -> Value {
        let rhs_block = self.builder.create_block();
        self.func_writer[rhs_block] = "logical_and_compute_rhs".into();
        let exit_block = self.builder.create_block();
        self.func_writer[exit_block] = "logical_and_exit".into();

        // if lhs is true, test the rhs
        // if lhs is false, exit early
        let lhs = lhs(self);
        self.builder
            .ins()
            .brif(lhs, rhs_block, &[], exit_block, &[BlockArg::Value(lhs)]);

        self.builder.switch_to_block(rhs_block);
        self.builder.seal_block(rhs_block);

        let rhs = rhs(self);
        self.builder.ins().jump(exit_block, &[BlockArg::Value(rhs)]);

        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(exit_block);

        self.builder.append_block_param(exit_block, types::I8)
    }

    fn logical_or(
        &mut self,
        lhs: impl FnOnce(&mut Self) -> Value,
        rhs: impl FnOnce(&mut Self) -> Value,
    ) -> Value {
        let rhs_block = self.builder.create_block();
        self.func_writer[rhs_block] = "logical_or_compute_rhs".into();
        let exit_block = self.builder.create_block();
        self.func_writer[exit_block] = "logical_or_exit".into();

        // if the lhs is true, exit early
        // if the lhs is false, test the rhs
        let lhs = lhs(self);
        self.builder
            .ins()
            .brif(lhs, exit_block, &[BlockArg::Value(lhs)], rhs_block, &[]);

        self.builder.switch_to_block(rhs_block);
        self.builder.seal_block(rhs_block);

        let rhs = rhs(self);
        self.builder.ins().jump(exit_block, &[BlockArg::Value(rhs)]);

        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(exit_block);

        self.builder.append_block_param(exit_block, types::I8)
    }

    fn compile_builtin_global(&mut self, builtin: BuiltinGlobal) -> DataId {
        match builtin {
            builtin::BuiltinGlobal::ArrayLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .array_layout_slice
            }
            builtin::BuiltinGlobal::DistinctLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .distinct_layout_slice
            }
            builtin::BuiltinGlobal::StructLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .struct_layout_slice
            }
            builtin::BuiltinGlobal::EnumLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .enum_layout_slice
            }
            builtin::BuiltinGlobal::VariantLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .variant_layout_slice
            }
            builtin::BuiltinGlobal::OptionalLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .optional_layout_slice
            }
            builtin::BuiltinGlobal::ErrorUnionLayouts => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .error_union_layout_slice
            }
            builtin::BuiltinGlobal::PointerLayout => {
                self.meta_tys
                    .layout_arrays
                    .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                    .pointer_layout
            }
            builtin::BuiltinGlobal::ArrayInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .array_info_slice
            }
            builtin::BuiltinGlobal::SliceInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .slice_info_slice
            }
            builtin::BuiltinGlobal::PointerInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .pointer_info_slice
            }
            builtin::BuiltinGlobal::DistinctInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .distinct_info_slice
            }
            builtin::BuiltinGlobal::StructInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .struct_info_slice
            }
            builtin::BuiltinGlobal::EnumInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .enum_info_slice
            }
            builtin::BuiltinGlobal::VariantInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .variant_info_slice
            }
            builtin::BuiltinGlobal::OptionalInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .optional_info_slice
            }
            builtin::BuiltinGlobal::ErrorUnionInfos => {
                self.meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .error_union_info_slice
            }
            builtin::BuiltinGlobal::CommandlineArgs => {
                *self.cmd_args_slice.get_or_insert_with(|| {
                    self.module
                        .declare_data(
                            &mangle::mangle_internal("commandline_args"),
                            Linkage::Export,
                            // it must be writable since that's what happens in the c main
                            // function
                            true,
                            false,
                        )
                        .expect("error declaring data")
                })
            }
        }
    }

    fn unnamed_func_to_local(&mut self, expr: Idx<hir::Expr>, lambda: Idx<hir::Lambda>) -> FuncRef {
        if let Some(func_ref) = self.local_lambdas.get(&lambda) {
            return *func_ref;
        }

        let (param_tys, return_ty) = self.tys[self.file_name][expr].as_function().unwrap();

        let sig = Into::<Abi>::into(self.module.target_config())
            .fn_to_target((&param_tys, return_ty))
            .to_cl(self.ptr_ty, self.module.target_config().default_call_conv);

        let ftc = FunctionToCompile {
            file_name: self.file_name,
            function_name: None,
            lambda,
            param_tys,
            return_ty,
        };

        let mangled = ftc.to_mangled_name(self.mod_dir, self.interner);

        self.functions_to_compile.push_back(ftc);

        let func_id = self
            .module
            .declare_function(&mangled, Linkage::Export, &sig)
            .unwrap();

        let local_func = self.module.declare_func_in_func(func_id, self.builder.func);

        self.local_lambdas.insert(lambda, local_func);

        local_func
    }

    pub fn compile_unreachablez(&mut self, condition: Value, message: Option<&str>) {
        let pass = self.builder.create_block();
        self.func_writer[pass] = "unreachable_check_okay".into();
        let fail = self.builder.create_block();
        self.func_writer[fail] = "unreachable_check_failure".into();
        self.builder.set_cold_block(fail);

        self.builder.ins().brif(condition, pass, &[], fail, &[]);

        self.builder.switch_to_block(fail);
        self.builder.seal_block(fail);

        self.compile_unreachable(message);

        self.builder.switch_to_block(pass);
        self.builder.seal_block(pass);
    }

    /// The default message is "Entered unreachable code"
    pub fn compile_unreachable(&mut self, message: Option<&str>) {
        // print message
        let puts = self.get_or_create_extern_func_id(
            "puts",
            vec![AbiParam::new(self.ptr_ty)],
            vec![AbiParam::new(types::I32)],
        );
        let puts = self.module.declare_func_in_func(puts, self.builder.func);

        let mut msg = format!(
            "\n\nin {} : entered unreachable code",
            self.file_name.to_string(self.mod_dir, self.interner),
        );
        if let Some(message) = message {
            msg.push_str(": ");
            msg.push_str(message);
        }

        let data = self.create_global_str(msg);
        let local_id = self.module.declare_data_in_func(data, self.builder.func);
        let string = self.builder.ins().symbol_value(self.ptr_ty, local_id);

        self.builder.ins().call(puts, &[string]);

        // exit program

        let exit =
            self.get_or_create_extern_func_id("exit", vec![AbiParam::new(types::I32)], vec![]);
        let exit = self.module.declare_func_in_func(exit, self.builder.func);

        let exit_code = self.builder.ins().iconst(types::I32, 1);
        self.builder.ins().call(exit, &[exit_code]);

        // trap for good measure

        self.builder.ins().trap(TRAP_UNREACHABLE);
    }

    pub fn compile_and_cast(&mut self, expr: Idx<hir::Expr>, cast_to: Intern<Ty>) -> Option<Value> {
        let value = self.compile_expr(expr);

        self.cast(value, self.tys[self.file_name][expr], cast_to)
    }

    pub fn compile_and_cast_with_args(
        &mut self,
        expr: Idx<hir::Expr>,
        no_load: bool,
        cast_to: Intern<Ty>,
    ) -> Option<Value> {
        let value = self.compile_expr_with_args(expr, no_load);

        self.cast(value, self.tys[self.file_name][expr], cast_to)
    }

    pub fn compile_and_cast_into_memory(
        &mut self,
        expr: Idx<hir::Expr>,
        cast_to: Intern<Ty>,
        memory: MemoryLoc,
    ) -> Option<Value> {
        if self.tys[self.file_name][expr].is_functionally_equivalent_to(&cast_to, true) {
            self.store_expr_in_memory(expr, cast_to, memory);

            return Some(memory.into_value(&mut self.builder, self.ptr_ty));
        }

        // todo: there should be a function similar to `store_expr_in_memory` that also casts along
        // the way. this would remove an unnecessary memcpy
        let value = self.compile_expr(expr);

        // println!(
        //     "compile_and_cast_into_memory {} #{} : {:?} ({:?}) -> {:?} ({:?})",
        //     self.file_name.debug(self.interner),
        //     expr.into_raw(),
        //     value,
        //     self.tys[self.file_name][expr],
        //     memory,
        //     cast_to
        // );

        self.cast_into_memory(value, self.tys[self.file_name][expr], cast_to, memory)
    }

    fn cast_into_memory(
        &mut self,
        val: Option<Value>,
        cast_from: Intern<Ty>,
        cast_to: Intern<Ty>,
        memory: MemoryLoc,
    ) -> Option<Value> {
        super::cast_into_memory(
            self.meta_tys,
            self.module,
            &mut self.builder,
            &mut self.func_writer,
            self.ptr_ty,
            val,
            cast_from,
            cast_to,
            Some(memory),
        )
    }

    /// This takes an Option because a `()` might be automatically casted to an `any`.
    /// This returns an Option because `()` might not be automatically casted to an `any`.
    fn cast(
        &mut self,
        val: Option<Value>,
        cast_from: Intern<Ty>,
        cast_to: Intern<Ty>,
    ) -> Option<Value> {
        super::cast_into_memory(
            self.meta_tys,
            self.module,
            &mut self.builder,
            &mut self.func_writer,
            self.ptr_ty,
            val,
            cast_from,
            cast_to,
            None,
        )
    }
}

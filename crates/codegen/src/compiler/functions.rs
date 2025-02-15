use std::collections::VecDeque;

use cranelift::{
    codegen::ir::{Endianness, FuncRef},
    frontend::Switch,
    prelude::{
        types, Block, FloatCC, FunctionBuilder, InstBuilder, IntCC, MemFlags, StackSlotData,
        StackSlotKind, TrapCode, Value, Variable,
    },
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use hir::{FQComptime, LocalDef, ScopeId, SwitchLocal};
use hir_ty::{ComptimeResult, Ty};
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use uid_gen::UIDGenerator;

use crate::{
    builtin::{self, BuiltinFunction},
    convert::{GetFinalTy, ToTyId},
    layout::GetLayoutInfo,
    mangle::{self, Mangle},
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
    pub(crate) compiler_defined_functions: &'a mut FxHashMap<BuiltinFunction, FuncId>,
    pub(crate) globals: &'a mut FxHashMap<hir::Fqn, DataId>,
    pub(crate) str_id_gen: &'a mut UIDGenerator,
    pub(crate) i128_id_gen: &'a mut UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<FQComptime, ComptimeResult>,
    pub(crate) comptime_data: &'a mut FxHashMap<FQComptime, ComptimeData>,

    // variables
    pub(crate) var_id_gen: UIDGenerator,
    pub(crate) locals: FxHashMap<Idx<LocalDef>, Value>,
    pub(crate) switch_locals: FxHashMap<Idx<SwitchLocal>, Value>,
    pub(crate) params: FxHashMap<u64, Variable>,

    // for control flow (breaks and continues)
    pub(crate) exits: FxHashMap<ScopeId, Block>,
    pub(crate) continues: FxHashMap<ScopeId, Block>,
    pub(crate) defer_stack: Vec<DeferFrame>,
}

impl FunctionCompiler<'_> {
    pub(crate) fn finish(
        mut self,
        fn_abi: FnAbi,
        (args, return_ty): (&Vec<Intern<Ty>>, Intern<Ty>),
        function_body: Idx<hir::Expr>,
        debug_print: bool,
    ) {
        fn_abi.build_fn(&mut self, return_ty, args, function_body);

        if debug_print {
            print!("{}", self.builder.func);
        }

        self.builder.finalize();
    }

    /// Returns `None` if any inner comptime blocks haven't been evaluated yet
    fn expr_to_const_data(
        &mut self,
        file_name: hir::FileName,
        expr: Idx<hir::Expr>,
    ) -> Result<Box<[u8]>, UnfinishedComptimeErr> {
        if let Some(meta_ty) = self.tys[file_name].get_meta_ty(expr) {
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
            hir::Expr::StringLiteral(mut text) => {
                text.push('\0');
                text.into_bytes().into()
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

                assert!(local_def.value.is_some(), "if the value doesn't exist, `get_const` should've returned non-const, and there should be an error before codegen");

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
            if let Some(builtin) =
                builtin::as_compiler_defined_global(fqn, self.mod_dir, self.interner)
            {
                return Ok(match builtin {
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
                    builtin::BuiltinGlobal::PointerLayout => {
                        self.meta_tys
                            .layout_arrays
                            .get_or_insert_with(|| MetaTyLayoutArrays::new(self.module))
                            .pointer_layout
                    }
                    builtin::BuiltinGlobal::ArrayInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .array_info_slice
                    }
                    builtin::BuiltinGlobal::SliceInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .slice_info_slice
                    }
                    builtin::BuiltinGlobal::PointerInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .pointer_info_slice
                    }
                    builtin::BuiltinGlobal::DistinctInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .distinct_info_slice
                    }
                    builtin::BuiltinGlobal::StructInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .struct_info_slice
                    }
                    builtin::BuiltinGlobal::EnumInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .enum_info_slice
                    }
                    builtin::BuiltinGlobal::VariantInfo => {
                        self.meta_tys
                            .info_arrays
                            .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                            .variant_info_slice
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
                });
            }

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

        let bytes = self.expr_to_const_data(fqn.file, value)?;

        let global = self.create_global_data(
            &fqn.to_mangled_name(self.mod_dir, self.interner),
            true,
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
                export,
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
            self.compiler_defined_functions,
            self.functions_to_compile,
            self.tys,
            self.world_bodies,
            self.interner,
            fqn,
        )
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

                self.compile_and_cast_into_memory(assign_body.value, *dest_ty, dest);
            }
            hir::Stmt::Break {
                label: Some(label),
                value,
                ..
            } => {
                let exit_block = self.exits[&label];

                let value = value.and_then(|value| {
                    let referenced_block_ty =
                        self.tys[self.file_name][self.world_bodies[self.file_name][label]];

                    self.compile_and_cast(value, referenced_block_ty)
                });

                // run all the defers from here, backwards to the one we are breaking out of

                let mut used_frames = Vec::new();

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

                    // do this in reverse for the reasons explained in the Expr::Block code
                    for defer in frame.defers.iter().rev() {
                        self.compile_expr(*defer);
                    }

                    used_frames.push(self.defer_stack.pop().unwrap());
                }

                self.defer_stack.extend(used_frames.into_iter().rev());

                if let Some(value) = value {
                    self.builder.ins().jump(exit_block, &[value]);
                } else {
                    self.builder.ins().jump(exit_block, &[]);
                };
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
            Ty::Array { size, sub_ty, .. } => {
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
            Ty::File(_) => unreachable!("files do not have default values"),
            Ty::Function { .. } => unreachable!("functions do not have default values"),
            Ty::Struct { members, .. } => {
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
            Ty::Variant { sub_ty, .. } => {
                self.store_default_in_memory(*sub_ty, memory);
                return;
            }
            // void is just a no-op
            Ty::Void => return,
            Ty::NoEval => return,
        };

        memory.store(&mut self.builder, value, 0);
    }

    fn store_expr_in_memory(
        &mut self,
        expr: Idx<hir::Expr>,
        expected_ty: Intern<Ty>,
        memory: MemoryLoc,
    ) {
        let expr_ty = self.tys[self.file_name][expr];

        // if the expression has to be casted in order to become the expected type, do that.
        // the one cast this applies to is `core.Any` casting.
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

                memory.write(val, expected_ty, self.module, &mut self.builder);
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
        if let Some(meta_ty) = self.tys[self.file_name].get_meta_ty(expr) {
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
                let data = self.create_global_str(text);

                let local_id = self.module.declare_data_in_func(data, self.builder.func);

                Some(self.builder.ins().symbol_value(self.ptr_ty, local_id))
            }
            hir::Expr::CharLiteral(char) => Some(self.builder.ins().iconst(types::I8, char as i64)),
            hir::Expr::ArrayDecl { .. } => None,
            hir::Expr::ArrayLiteral { items, .. } => {
                let ty = self.tys[self.file_name][expr];

                if ty.is_zero_sized() {
                    return None;
                }

                let (_, sub_ty) = ty.as_array().expect("array literals must have array types");

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

                let good_index_block = self.builder.create_block();
                let bad_index_block = self.builder.create_block();

                let is_good_index =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThan, naive_index, len);
                self.builder
                    .ins()
                    .brif(is_good_index, good_index_block, &[], bad_index_block, &[]);

                self.builder.switch_to_block(bad_index_block);
                self.builder.set_cold_block(bad_index_block);
                self.builder.seal_block(bad_index_block);

                self.builder.ins().trap(TRAP_UNREACHABLE);

                self.builder.switch_to_block(good_index_block);
                self.builder.seal_block(good_index_block);

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

                    let expr = self.compile_expr(expr).unwrap();

                    self.builder.ins().stack_store(expr, stack_slot, 0);

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
            } => {
                match op {
                    hir::BinaryOp::LAnd => {
                        let rhs_block = self.builder.create_block();
                        let exit_block = self.builder.create_block();

                        // if lhs is true, test the rhs
                        // if lhs is false, exit early
                        let lhs = self.compile_expr(lhs_expr).unwrap();
                        self.builder
                            .ins()
                            .brif(lhs, rhs_block, &[], exit_block, &[lhs]);

                        self.builder.switch_to_block(rhs_block);
                        self.builder.seal_block(rhs_block);

                        let rhs = self.compile_expr(rhs_expr).unwrap();
                        self.builder.ins().jump(exit_block, &[rhs]);

                        self.builder.switch_to_block(exit_block);
                        self.builder.seal_block(exit_block);
                        let result = self.builder.append_block_param(exit_block, types::I8);

                        return Some(result);
                    }
                    hir::BinaryOp::LOr => {
                        let rhs_block = self.builder.create_block();
                        let exit_block = self.builder.create_block();

                        // if the lhs is true, exit early
                        // if the lhs is false, test the rhs
                        let lhs = self.compile_expr(lhs_expr).unwrap();
                        self.builder
                            .ins()
                            .brif(lhs, exit_block, &[lhs], rhs_block, &[]);

                        self.builder.switch_to_block(rhs_block);
                        self.builder.seal_block(rhs_block);

                        let rhs = self.compile_expr(rhs_expr).unwrap();
                        self.builder.ins().jump(exit_block, &[rhs]);

                        self.builder.switch_to_block(exit_block);
                        self.builder.seal_block(exit_block);
                        let result = self.builder.append_block_param(exit_block, types::I8);

                        return Some(result);
                    }
                    _ => {}
                }

                let lhs = self.compile_expr(lhs_expr).unwrap();
                let rhs = self.compile_expr(rhs_expr).unwrap_or_else(|| {
                    println!("{:#?}", self.world_bodies[self.file_name][rhs_expr].clone());
                    panic!(
                        "{}#{} is None",
                        self.interner.lookup(self.file_name.0),
                        rhs_expr.into_raw()
                    );
                });

                let lhs_ty = self.tys[self.file_name][lhs_expr]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap();
                let rhs_ty = self.tys[self.file_name][rhs_expr]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap();

                let max_ty = lhs_ty.max(rhs_ty);

                // we need to make sure that both types are the same before we can do any operations on them
                let lhs = super::cast_num(&mut self.builder, lhs, lhs_ty, max_ty);
                let rhs = super::cast_num(&mut self.builder, rhs, rhs_ty, max_ty);

                if max_ty.float {
                    Some(match op {
                        hir::BinaryOp::Add => self.builder.ins().fadd(lhs, rhs),
                        hir::BinaryOp::Sub => self.builder.ins().fsub(lhs, rhs),
                        hir::BinaryOp::Mul => self.builder.ins().fmul(lhs, rhs),
                        hir::BinaryOp::Div => self.builder.ins().fdiv(lhs, rhs),
                        hir::BinaryOp::Mod => unreachable!(),
                        hir::BinaryOp::Lt => self.builder.ins().fcmp(FloatCC::LessThan, lhs, rhs),
                        hir::BinaryOp::Gt => {
                            self.builder.ins().fcmp(FloatCC::GreaterThan, lhs, rhs)
                        }
                        hir::BinaryOp::Le => {
                            self.builder.ins().fcmp(FloatCC::LessThanOrEqual, lhs, rhs)
                        }
                        hir::BinaryOp::Ge => {
                            self.builder
                                .ins()
                                .fcmp(FloatCC::GreaterThanOrEqual, lhs, rhs)
                        }
                        hir::BinaryOp::Eq => self.builder.ins().fcmp(FloatCC::Equal, lhs, rhs),
                        hir::BinaryOp::Ne => self.builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs),
                        hir::BinaryOp::BAnd => self.builder.ins().band(lhs, rhs),
                        hir::BinaryOp::BOr => self.builder.ins().bor(lhs, rhs),
                        hir::BinaryOp::Xor => self.builder.ins().bxor(lhs, rhs),
                        hir::BinaryOp::LShift | hir::BinaryOp::RShift => unreachable!(),
                        hir::BinaryOp::LAnd | hir::BinaryOp::LOr => unreachable!(),
                    })
                } else {
                    Some(match op {
                        hir::BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
                        hir::BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
                        hir::BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
                        hir::BinaryOp::Div => {
                            if max_ty.signed {
                                self.builder.ins().sdiv(lhs, rhs)
                            } else {
                                self.builder.ins().udiv(lhs, rhs)
                            }
                        }
                        hir::BinaryOp::Mod => {
                            if max_ty.signed {
                                self.builder.ins().srem(lhs, rhs)
                            } else {
                                self.builder.ins().urem(lhs, rhs)
                            }
                        }
                        hir::BinaryOp::Lt => {
                            if max_ty.signed {
                                self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs)
                            } else {
                                self.builder.ins().icmp(IntCC::UnsignedLessThan, lhs, rhs)
                            }
                        }
                        hir::BinaryOp::Gt => {
                            if max_ty.signed {
                                self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs)
                            } else {
                                self.builder
                                    .ins()
                                    .icmp(IntCC::UnsignedGreaterThan, lhs, rhs)
                            }
                        }
                        hir::BinaryOp::Le => {
                            if max_ty.signed {
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
                            if max_ty.signed {
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
                            if max_ty.signed {
                                self.builder.ins().sshr(lhs, rhs)
                            } else {
                                self.builder.ins().ushr(lhs, rhs)
                            }
                        }
                        hir::BinaryOp::LAnd | hir::BinaryOp::LOr => unreachable!(),
                    })
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr_ty = self.tys[self.file_name][expr]
                    .get_final_ty()
                    .into_number_type()
                    .unwrap();

                let expr = self.compile_expr(expr).unwrap();

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

                let arg_values = args
                    .iter()
                    .zip(param_tys.iter())
                    .filter_map(|(arg_expr, expected_ty)| {
                        self.compile_and_cast(*arg_expr, *expected_ty)
                    })
                    .collect::<Vec<_>>();
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
            hir::Expr::Paren(Some(expr)) => self.compile_expr_with_args(expr, no_load),
            hir::Expr::Paren(None) => None,
            hir::Expr::Block { stmts, tail_expr } => {
                let expr_ty = self.tys[self.file_name][expr];
                let final_ty = expr_ty.get_final_ty();

                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();
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
                                && *self.tys[self.file_name][expr] == Ty::NoEval =>
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
                            let value = self.compile_expr_with_args(tail_expr, no_load);
                            if scope_id.is_none()
                                && *self.tys[self.file_name][tail_expr] == Ty::NoEval
                            {
                                no_eval = true;
                            }
                            value
                        })
                    })
                    .flatten();

                if !no_eval {
                    if let Some(value) = value {
                        self.builder.ins().jump(exit_block, &[value]);
                    } else if !expr_ty.is_void() && scope_id.is_some() {
                        // we know this block reaches it's end (it's !noeval)
                        //
                        // we also know it doesn't have a tail expression (because `value` was None)
                        //
                        // we also know it has a non-void type (no implicit tail expression)
                        //
                        // since it doesn't have a tail expression, the type checker has already
                        // confirmed that it *must* always reach a break to it's own end.
                        //
                        // this break has to be somewhere deep in an grandchild block. we know it
                        // exists, and we know that this exact point is unreachable because of that
                        // break, and because of the absence of a tail expression.
                        //
                        // therefore it's safe to trap *here*, at the end of the `body_block`
                        //
                        // but we can't trap in the `exit_block`, since the `exit_block` *is*
                        // reachable.
                        //
                        // the reason we need to trap is because cranelift forces us to end all blocks with
                        // a "final" instruction (a jump or trap). we can't exactly jump to the exit
                        // because we don't have a value with which to jump (and remember the exit
                        // is expecting something non-void). so since it's safe to trap, we just trap.
                        self.builder.ins().trap(TRAP_UNREACHABLE);
                    } else {
                        self.builder.ins().jump(exit_block, &[]);
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
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

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

                if *self.tys[self.file_name][body] == Ty::NoEval {
                    self.builder.ins().trap(TRAP_UNREACHABLE);
                } else {
                    match body_value {
                        Some(then_value) => {
                            self.builder.ins().jump(merge_block, &[then_value]);
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

                    if *self.tys[self.file_name][else_branch] == Ty::NoEval {
                        self.builder.ins().trap(TRAP_UNREACHABLE);
                    } else {
                        match else_value {
                            Some(then_value) => {
                                self.builder.ins().jump(merge_block, &[then_value]);
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
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

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
                let body_block = self.builder.create_block();
                let fallback_block = self.builder.create_block();
                let arm_blocks: FxHashMap<_, _> = arms
                    .iter()
                    .map(|arm| {
                        (
                            arm.variant_name
                                .expect("if codegen is running, no names should be `None`")
                                .name,
                            (self.builder.create_block(), *arm),
                        )
                    })
                    .collect();
                let exit_block = self.builder.create_block();

                let enum_ty = self.tys[self.file_name][scrutinee];
                let Ty::Enum {
                    variants: variant_tys,
                    ..
                } = enum_ty.as_ref()
                else {
                    unreachable!("the scrutinee should be an enum")
                };
                let enum_layout = enum_ty.enum_layout().unwrap();

                let return_ty = self.tys[self.file_name][expr];
                let return_ty_real = return_ty.get_final_ty().into_real_type();

                if let Some(ty) = return_ty_real {
                    self.builder.append_block_param(exit_block, ty);
                }

                self.builder.ins().jump(body_block, &[]);
                self.builder.seal_block(body_block);
                self.builder.switch_to_block(body_block);

                let scrutinee_val = self
                    .compile_expr(scrutinee)
                    .expect("enums are never zero sized");
                let discrim_val = self.builder.ins().load(
                    types::I8,
                    MemFlags::trusted(),
                    scrutinee_val,
                    enum_layout.discriminant_offset() as i32,
                );

                let mut switch = Switch::new();
                for variant_ty in variant_tys {
                    let Ty::Variant {
                        variant_name,
                        discriminant,
                        ..
                    } = variant_ty.as_ref()
                    else {
                        unreachable!("all variants should be `Ty::Variant`")
                    };

                    let Some(arm) = arm_blocks.get(variant_name) else {
                        continue;
                    };

                    // todo: maybe discriminant should also be u128
                    switch.set_entry(*discriminant as u128, arm.0);
                }

                switch.emit(&mut self.builder, discrim_val, fallback_block);

                {
                    self.builder.switch_to_block(fallback_block);
                    self.builder.seal_block(fallback_block);

                    if let Some(default) = default {
                        if let Some(switch_local) = default.switch_local {
                            self.switch_locals.insert(switch_local, scrutinee_val);
                        }

                        // todo: should no_load be used here?
                        let default_val =
                            self.compile_and_cast_with_args(default.body, no_load, return_ty);

                        if let Some(default_val) = default_val {
                            self.builder.ins().jump(exit_block, &[default_val]);
                        } else {
                            self.builder.ins().jump(exit_block, &[]);
                        }
                    } else {
                        self.builder.ins().trap(TRAP_UNREACHABLE);
                    }
                }

                for (arm_block, arm) in arm_blocks.values() {
                    self.builder.switch_to_block(*arm_block);
                    self.builder.seal_block(*arm_block);

                    if let Some(switch_local) = arm.switch_local {
                        self.switch_locals.insert(switch_local, scrutinee_val);
                    }

                    let body_val = self.compile_and_cast_with_args(arm.body, no_load, return_ty);

                    if let Some(body_val) = body_val {
                        self.builder.ins().jump(exit_block, &[body_val]);
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
            hir::Expr::SwitchLocal(switch_local) => {
                let ptr = *self.switch_locals.get(&switch_local)?;

                let ty = &self.tys[self.file_name][switch_local];

                if no_load || ty.is_aggregate() {
                    Some(ptr)
                } else {
                    let ty = ty.get_final_ty();

                    // if it isn't a real type, this will just return None
                    ty.into_real_type()
                        .map(|ty| self.builder.ins().load(ty, MemFlags::trusted(), ptr, 0))
                }
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

                        if source_ty.is_slice() {
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
                        } else if let Some((len, _)) = source_ty.as_array() {
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

                                let len = self.builder.ins().iconst(self.ptr_ty, len as i64);
                                self.builder.ins().stack_store(len, ss, 0);

                                return Some(self.builder.ins().stack_addr(self.ptr_ty, ss, 0));
                            } else {
                                return Some(self.builder.ins().iconst(self.ptr_ty, len as i64));
                            }
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
            hir::Expr::Import(_) => None,
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
                    let compute_block = self.builder.create_block();
                    let exit_block = self.builder.create_block();

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

                        self.builder.ins().jump(exit_block, &[value]);
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

                        self.builder.ins().jump(exit_block, &[value]);
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
            self.ptr_ty,
            val,
            cast_from,
            cast_to,
            Some(memory),
        )
    }

    /// This takes an Option and returns an Option because a `()` might be automatically casted to
    /// a `core.Any`
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
            self.ptr_ty,
            val,
            cast_from,
            cast_to,
            None,
        )
    }
}

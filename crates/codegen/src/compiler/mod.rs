pub mod comptime;
mod functions;
pub mod program;

use cranelift::codegen::ir::Endianness;
use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{
    types, FunctionBuilder, FunctionBuilderContext, InstBuilder, IntCC, MemFlags, StackSlotData,
    StackSlotKind, TrapCode, Value,
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir_ty::Ty;
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::builtin::{as_compiler_defined, BuiltinFunction};
use crate::layout::{self, GetLayoutInfo};
use crate::mangle::{self, Mangle};
use crate::{
    convert::{self, *},
    ComptimeToCompile, FinalSignature, Verbosity,
};

use self::comptime::ComptimeResult;
use self::functions::FunctionCompiler;

#[derive(Default)]
pub(crate) struct MetaTyData {
    pub(crate) tys_to_compile: Vec<Intern<Ty>>,

    pub(crate) array_uid_gen: UIDGenerator,
    pub(crate) slice_uid_gen: UIDGenerator,
    pub(crate) pointer_uid_gen: UIDGenerator,
    pub(crate) distinct_uid_gen: UIDGenerator,
    pub(crate) function_uid_gen: UIDGenerator,
    pub(crate) struct_uid_gen: UIDGenerator,

    pub(crate) mem_arrays: Option<MetaTyMemArrays>,
    pub(crate) info_arrays: Option<MetaTyInfoArrays>,
}

pub(crate) struct MetaTyMemArrays {
    pub(crate) array_mem: DataId,
    pub(crate) distinct_mem: DataId,
    pub(crate) struct_mem: DataId,
}

impl MetaTyMemArrays {
    pub(crate) fn new(module: &mut dyn Module) -> Self {
        Self {
            array_mem: module
                .declare_data(
                    &mangle::mangle_internal("array_type_mem"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
            distinct_mem: module
                .declare_data(
                    &mangle::mangle_internal("distinct_type_mem"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
            struct_mem: module
                .declare_data(
                    &mangle::mangle_internal("struct_type_mem"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
        }
    }
}

pub(crate) struct MetaTyInfoArrays {
    pub(crate) array_info: DataId,
    pub(crate) slice_info: DataId,
    pub(crate) pointer_info: DataId,
    pub(crate) distinct_info: DataId,
}

impl MetaTyInfoArrays {
    pub(crate) fn new(module: &mut dyn Module) -> Self {
        Self {
            array_info: module
                .declare_data(
                    &mangle::mangle_internal("array_type_info"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
            slice_info: module
                .declare_data(
                    &mangle::mangle_internal("slice_type_info"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
            pointer_info: module
                .declare_data(
                    &mangle::mangle_internal("pointer_type_info"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
            distinct_info: module
                .declare_data(
                    &mangle::mangle_internal("distinct_type_info"),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data"),
        }
    }
}

pub(crate) struct FunctionToCompile {
    pub(crate) file_name: hir::FileName,
    pub(crate) function_name: Option<hir::Name>,
    pub(crate) lambda: Idx<hir::Lambda>,
    pub(crate) param_tys: Vec<Intern<Ty>>,
    pub(crate) return_ty: Intern<Ty>,
}

pub(crate) struct Compiler<'a> {
    pub(crate) verbosity: Verbosity,

    pub(crate) mod_dir: &'a std::path::Path,

    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
    pub(crate) tys: &'a hir_ty::InferenceResult,

    pub(crate) builder_context: FunctionBuilderContext,
    pub(crate) ctx: codegen::Context,
    pub(crate) data_description: DataDescription,
    pub(crate) module: &'a mut dyn Module,
    pub(crate) pointer_ty: types::Type,

    // bodies to compile
    pub(crate) functions_to_compile: VecDeque<FunctionToCompile>,

    // globals
    pub(crate) functions: FxHashMap<hir::Fqn, FuncId>,
    pub(crate) compiler_defined_functions: FxHashMap<BuiltinFunction, FuncId>,
    pub(crate) data: FxHashMap<hir::Fqn, DataId>,
    pub(crate) meta_tys: MetaTyData,
    pub(crate) str_id_gen: UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<ComptimeToCompile, ComptimeResult>,
}

impl Compiler<'_> {
    fn finalize_tys(&mut self) {
        layout::calc_layouts(self.tys.all_tys(), self.pointer_ty.bits());
        convert::calc_finals(self.tys.all_tys(), self.pointer_ty);
    }

    fn compile_queued(&mut self) {
        while let Some(ftc) = self.functions_to_compile.pop_front() {
            self.compile_ftc(ftc);
        }

        fn extend_with_bytes(
            list: &mut Vec<u8>,
            num: u32,
            target_bit_width: u8,
            endianness: Endianness,
        ) {
            match (target_bit_width, endianness) {
                (8, Endianness::Big) => list.extend((num as u8).to_be_bytes()),
                (8, Endianness::Little) => list.extend((num as u8).to_le_bytes()),
                (16, Endianness::Big) => list.extend((num as u16).to_be_bytes()),
                (16, Endianness::Little) => list.extend((num as u16).to_le_bytes()),
                #[allow(clippy::unnecessary_cast)]
                (32, Endianness::Big) => list.extend((num as u32).to_be_bytes()),
                #[allow(clippy::unnecessary_cast)]
                (32, Endianness::Little) => list.extend((num as u32).to_le_bytes()),
                (64, Endianness::Big) => list.extend((num as u64).to_be_bytes()),
                (64, Endianness::Little) => list.extend((num as u64).to_le_bytes()),
                _ => unreachable!(),
            }
        }

        let mut array_mem_data = Vec::new();
        let mut distinct_mem_data = Vec::new();
        let mut struct_mem_data = Vec::new();

        let mut array_info_data = Vec::new();
        let mut slice_info_data = Vec::new();
        let mut pointer_info_data = Vec::new();
        let mut distinct_info_data = Vec::new();

        for ty in &self.meta_tys.tys_to_compile {
            'mem: {
                if self.meta_tys.mem_arrays.is_some() {
                    let data = match ty.as_ref() {
                        Ty::Array { .. } => &mut array_mem_data,
                        Ty::Distinct { .. } => &mut distinct_mem_data,
                        Ty::Struct { .. } => &mut struct_mem_data,
                        _ => break 'mem,
                    };

                    let size = ty.size();
                    let align = ty.align();

                    extend_with_bytes(
                        data,
                        size,
                        self.pointer_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                    extend_with_bytes(
                        data,
                        align,
                        self.pointer_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                }
            }

            if self.meta_tys.info_arrays.is_some() {
                match ty.as_ref() {
                    Ty::Array { size, sub_ty } => {
                        extend_with_bytes(
                            &mut array_info_data,
                            (*size) as u32,
                            self.pointer_ty.bits() as u8,
                            self.module.isa().endianness(),
                        );

                        let ptr_size = self.pointer_ty.bytes();
                        let padding = layout::padding_needed_for(ptr_size, (32 / 8).min(8));

                        array_info_data.extend(std::iter::repeat(0).take(padding as usize));

                        extend_with_bytes(
                            &mut array_info_data,
                            sub_ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Slice { sub_ty } => {
                        extend_with_bytes(
                            &mut slice_info_data,
                            sub_ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Pointer { sub_ty, .. } => {
                        extend_with_bytes(
                            &mut pointer_info_data,
                            sub_ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Distinct { sub_ty: ty, .. } => {
                        extend_with_bytes(
                            &mut distinct_info_data,
                            ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    _ => continue,
                }
            }
        }

        fn define(
            module: &mut dyn Module,
            data_desc: &mut DataDescription,
            info_array: DataId,
            bytes: Vec<u8>,
        ) {
            data_desc.define(bytes.into_boxed_slice());
            module
                .define_data(info_array, data_desc)
                .expect("error defining data");
            data_desc.clear();
        }

        if let Some(mem_arrays) = &self.meta_tys.mem_arrays {
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.array_mem,
                array_mem_data,
            );
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.distinct_mem,
                distinct_mem_data,
            );
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.struct_mem,
                struct_mem_data,
            );
        }
        if let Some(info_arrays) = &self.meta_tys.info_arrays {
            define(
                self.module,
                &mut self.data_description,
                info_arrays.array_info,
                array_info_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.slice_info,
                slice_info_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.pointer_info,
                pointer_info_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.distinct_info,
                distinct_info_data,
            );
        }
    }

    fn get_func_id(&mut self, fqn: hir::Fqn) -> FuncId {
        get_func_id(
            self.module,
            self.pointer_ty,
            self.mod_dir,
            &mut self.functions,
            &mut self.compiler_defined_functions,
            &mut self.functions_to_compile,
            self.tys,
            self.bodies_map,
            self.interner,
            fqn,
        )
    }

    fn compile_ftc(&mut self, ftc: FunctionToCompile) {
        let hir::Lambda {
            body, is_extern, ..
        } = &self.bodies_map[&ftc.file_name][ftc.lambda];

        if *is_extern {
            if let Some(compiler_defined) =
                as_compiler_defined(*is_extern, &ftc, self.mod_dir, self.interner)
            {
                let (mangled, sig, func_id) = compiler_defined.to_sig_and_func_id(
                    self.module,
                    self.pointer_ty,
                    self.mod_dir,
                    self.interner,
                );

                match compiler_defined {
                    BuiltinFunction::PtrBitcast => {
                        self.compile_ptr_bitcast_fn(&mangled, sig, func_id)
                    }
                    BuiltinFunction::SizeOf => {
                        self.compile_meta_layout(&mangled, sig, func_id, true)
                    }
                    BuiltinFunction::AlignOf => {
                        self.compile_meta_layout(&mangled, sig, func_id, false)
                    }
                    BuiltinFunction::IsMetaOfType(discriminant) => {
                        self.compile_meta_is_of_type(&mangled, sig, func_id, discriminant)
                    }
                    BuiltinFunction::GetMetaInfo(discriminant) => {
                        self.compile_meta_info(&mangled, sig, func_id, discriminant);
                    }
                }
            }
            return;
        }

        let unmangled_name = if let Some(name) = ftc.function_name {
            let fqn = hir::Fqn {
                file: ftc.file_name,
                name,
            };

            fqn.to_string(self.mod_dir, self.interner)
        } else {
            format!(
                "{}.lambda#{}",
                ftc.file_name.to_string(self.mod_dir, self.interner),
                ftc.lambda.into_raw()
            )
        };

        self.compile_real_function(
            &unmangled_name,
            &ftc.to_mangled_name(self.mod_dir, self.interner),
            ftc.file_name,
            *body,
            ftc.param_tys,
            ftc.return_ty,
        );
    }

    fn compile_ptr_bitcast_fn(&mut self, mangled_name: &str, sig: FinalSignature, func_id: FuncId) {
        self.ctx.func.signature = sig;

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        builder.switch_to_block(entry_block);
        // tell the builder that the block will have no further predecessors
        builder.seal_block(entry_block);

        // this function literally just returns what it was given.
        // the only purpose of this function is to bypass `hir_ty`.
        // could we make calls to `ptr.from_raw()` or `ptr.to_raw()`
        // just evaluate to the first argument? yes probably
        // we probably only need to compile these builtin functions
        // if they are used as first class functions
        let arg_ptr = builder.append_block_param(entry_block, self.pointer_ty);
        builder.ins().return_(&[arg_ptr]);

        builder.seal_all_blocks();
        builder.finalize();

        if self.verbosity == Verbosity::AllFunctions {
            println!(
                "ptr_bitcast \x1B[90m{}\x1B[0m:\n{}",
                mangled_name, self.ctx.func
            );
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .unwrap_or_else(|err| {
                println!("Error defining function:");
                if let ModuleError::Compilation(CodegenError::Verifier(v)) = err {
                    println!("{}", v.to_string().replace("):", "):\n "));
                } else {
                    println!("{:?}", err);
                }
                std::process::exit(1);
            });

        self.module.clear_context(&mut self.ctx);
    }

    fn compile_meta_layout(
        &mut self,
        mangled_name: &str,
        sig: FinalSignature,
        func_id: FuncId,
        size: bool,
    ) {
        self.ctx.func.signature = sig;

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        builder.switch_to_block(entry_block);
        // tell the builder that the block will have no further predecessors
        builder.seal_block(entry_block);

        builder.append_block_params_for_function_params(entry_block);

        let simple_handler = builder.create_block();
        let struct_check = builder.create_block();

        let ty_arg = builder.block_params(entry_block)[0];

        let discriminant = builder.ins().ushr_imm(ty_arg, 26);

        let is_simple = builder.ins().icmp_imm(
            IntCC::UnsignedLessThan,
            discriminant,
            FIRST_COMPLEX_DISCRIMINANT as i64,
        );

        builder
            .ins()
            .brif(is_simple, simple_handler, &[], struct_check, &[]);

        builder.switch_to_block(simple_handler);
        builder.seal_block(simple_handler);

        let result = if size {
            // the first five bits hold the size
            builder.ins().band_imm(ty_arg, 0b11111)
        } else {
            let shifted = builder.ins().ushr_imm(ty_arg, 5);
            // after the size are four bits for the alignment
            builder.ins().band_imm(shifted, 0b1111)
        };

        let result = cast_num(
            &mut builder,
            result,
            NumberType {
                ty: types::I32,
                float: false,
                signed: false,
            },
            NumberType {
                ty: self.pointer_ty,
                float: false,
                signed: false,
            },
        );

        builder.ins().return_(&[result]);

        builder.switch_to_block(struct_check);
        builder.seal_block(struct_check);
        builder.set_cold_block(struct_check);

        // we will now check the type id, and depending on which complex it is, goto `complex_get`
        // with the proper type info array. I kinda just decided on the following order to check,
        // to try and reduce branch mispredictions, but it's very arbitrary

        let distinct_check = builder.create_block();
        let array_check = builder.create_block();
        let slice_check = builder.create_block();
        let slice_get = builder.create_block();
        let pointer_get = builder.create_block();

        let complex_get = builder.create_block();
        builder.append_block_param(complex_get, self.pointer_ty);

        // setup the memory info arrays

        let info_arrays = self
            .meta_tys
            .mem_arrays
            .get_or_insert_with(|| MetaTyMemArrays::new(self.module));

        let array_info = self
            .module
            .declare_data_in_func(info_arrays.array_mem, builder.func);
        let array_info = builder.ins().symbol_value(self.pointer_ty, array_info);

        let distinct_info = self
            .module
            .declare_data_in_func(info_arrays.distinct_mem, builder.func);
        let distinct_info = builder.ins().symbol_value(self.pointer_ty, distinct_info);

        let struct_info = self
            .module
            .declare_data_in_func(info_arrays.struct_mem, builder.func);
        let struct_info = builder.ins().symbol_value(self.pointer_ty, struct_info);

        // machine code to find the global array to use

        let is_struct =
            builder
                .ins()
                .icmp_imm(IntCC::Equal, discriminant, STRUCT_DISCRIMINANT as i64);
        builder
            .ins()
            .brif(is_struct, complex_get, &[struct_info], distinct_check, &[]);

        builder.switch_to_block(distinct_check);
        builder.seal_block(distinct_check);

        let is_distinct =
            builder
                .ins()
                .icmp_imm(IntCC::Equal, discriminant, DISTINCT_DISCRIMINANT as i64);
        builder
            .ins()
            .brif(is_distinct, complex_get, &[distinct_info], array_check, &[]);

        builder.switch_to_block(array_check);
        builder.seal_block(array_check);

        let is_array =
            builder
                .ins()
                .icmp_imm(IntCC::Equal, discriminant, ARRAY_DISCRIMINANT as i64);
        builder
            .ins()
            .brif(is_array, complex_get, &[array_info], slice_check, &[]);

        builder.switch_to_block(slice_check);
        builder.seal_block(slice_check);

        let is_slice =
            builder
                .ins()
                .icmp_imm(IntCC::Equal, discriminant, SLICE_DISCRIMINANT as i64);

        builder
            .ins()
            .brif(is_slice, slice_get, &[], pointer_get, &[]);

        builder.switch_to_block(slice_get);
        builder.seal_block(slice_get);

        let result = if size {
            builder
                .ins()
                .iconst(self.pointer_ty, self.pointer_ty.bytes() as i64 * 2)
        } else {
            builder
                .ins()
                .iconst(self.pointer_ty, self.pointer_ty.bytes().min(8) as i64)
        };

        builder.ins().return_(&[result]);

        builder.switch_to_block(pointer_get);
        builder.seal_block(pointer_get);

        let result = if size {
            builder
                .ins()
                .iconst(self.pointer_ty, self.pointer_ty.bytes() as i64)
        } else {
            builder
                .ins()
                .iconst(self.pointer_ty, self.pointer_ty.bytes().min(8) as i64)
        };

        builder.ins().return_(&[result]);

        builder.switch_to_block(complex_get);
        builder.seal_block(complex_get);

        // blacks out the discriminant (6 bits on the left hand side) from the typeid
        let index = builder.ins().band_imm(ty_arg, !(0b111111 << 26));
        // the stride of each complex array is usize * 2
        let byte_offset = builder
            .ins()
            .imul_imm(index, self.pointer_ty.bytes() as i64 * 2);

        let byte_offset = if size {
            byte_offset
        } else {
            builder
                .ins()
                .iadd_imm(byte_offset, self.pointer_ty.bytes() as i64)
        };

        let byte_offset = cast_num(
            &mut builder,
            byte_offset,
            NumberType {
                ty: types::I32,
                float: false,
                signed: false,
            },
            NumberType {
                ty: self.pointer_ty,
                float: false,
                signed: false,
            },
        );

        let info_array = builder.block_params(complex_get)[0];
        let actual_addr = builder.ins().iadd(info_array, byte_offset);

        let result = builder
            .ins()
            .load(self.pointer_ty, MemFlags::trusted(), actual_addr, 0);

        builder.ins().return_(&[result]);

        builder.seal_all_blocks();
        builder.finalize();

        if self.verbosity == Verbosity::AllFunctions {
            if size {
                print!("size_of");
            } else {
                print!("align_of");
            }
            println!(" \x1B[90m{}\x1B[0m:\n{}", mangled_name, self.ctx.func);
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .unwrap_or_else(|err| {
                println!("Error defining function:");
                if let ModuleError::Compilation(CodegenError::Verifier(v)) = err {
                    println!("{}", v.to_string().replace("):", "):\n "));
                } else {
                    println!("{:?}", err);
                }
                std::process::exit(1);
            });

        self.module.clear_context(&mut self.ctx);
    }

    fn compile_meta_is_of_type(
        &mut self,
        mangled_name: &str,
        sig: FinalSignature,
        func_id: FuncId,
        expected_disc: u32,
    ) {
        self.ctx.func.signature = sig;

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        builder.switch_to_block(entry_block);
        // tell the builder that the block will have no further predecessors
        builder.seal_block(entry_block);

        builder.append_block_params_for_function_params(entry_block);

        let ty_arg = builder.block_params(entry_block)[0];

        let discriminant = builder.ins().ushr_imm(ty_arg, 26);

        let is_of_type = builder
            .ins()
            .icmp_imm(IntCC::Equal, discriminant, expected_disc as i64);

        builder.ins().return_(&[is_of_type]);

        builder.seal_all_blocks();
        builder.finalize();

        if self.verbosity == Verbosity::AllFunctions {
            println!(
                "is_meta_{} \x1B[90m{}\x1B[0m:\n{}",
                expected_disc, mangled_name, self.ctx.func
            );
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .unwrap_or_else(|err| {
                println!("Error defining function:");
                if let ModuleError::Compilation(CodegenError::Verifier(v)) = err {
                    println!("{}", v.to_string().replace("):", "):\n "));
                } else {
                    println!("{:?}", err);
                }
                std::process::exit(1);
            });

        self.module.clear_context(&mut self.ctx);
    }

    fn compile_meta_info(
        &mut self,
        mangled_name: &str,
        sig: FinalSignature,
        func_id: FuncId,
        expected_disc: u32,
    ) {
        self.ctx.func.signature = sig;

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        builder.switch_to_block(entry_block);
        // tell the builder that the block will have no further predecessors
        builder.seal_block(entry_block);

        builder.append_block_params_for_function_params(entry_block);

        let right_type_block = builder.create_block();
        let wrong_type_block = builder.create_block();

        let ty_arg = builder.block_params(entry_block)[0];

        let discriminant = builder.ins().ushr_imm(ty_arg, 26);

        let is_of_type = builder
            .ins()
            .icmp_imm(IntCC::Equal, discriminant, expected_disc as i64);

        builder
            .ins()
            .brif(is_of_type, right_type_block, &[], wrong_type_block, &[]);

        builder.switch_to_block(right_type_block);
        builder.seal_block(right_type_block);

        let return_addr = builder.block_params(entry_block)[1];

        let build_offset = |builder: &mut FunctionBuilder<'_>, stride: u32| {
            // blacks out the discriminant (6 bits on the left hand side) from the typeid
            let index = builder.ins().band_imm(ty_arg, !(0b111111 << 26));
            let offset = builder.ins().imul_imm(index, stride as i64);
            cast_num(
                builder,
                offset,
                NumberType {
                    ty: types::I32,
                    float: false,
                    signed: false,
                },
                NumberType {
                    ty: self.pointer_ty,
                    float: false,
                    signed: false,
                },
            )
        };

        match expected_disc {
            INT_DISCRIMINANT => {
                let byte_width = builder.ins().band_imm(ty_arg, 0b11111);
                let bit_width = builder.ins().imul_imm(byte_width, 8);
                let bit_width = builder.ins().ireduce(types::I8, bit_width);

                builder
                    .ins()
                    .store(MemFlags::trusted(), bit_width, return_addr, 0);

                let signed = builder.ins().band_imm(ty_arg, 1 << 9);
                let signed = builder.ins().ushr_imm(signed, 9);
                let signed = builder.ins().ireduce(types::I8, signed);

                builder
                    .ins()
                    .store(MemFlags::trusted(), signed, return_addr, 1);
            }
            FLOAT_DISCRIMINANT => {
                let byte_width = builder.ins().band_imm(ty_arg, 0b11111);
                let bit_width = builder.ins().imul_imm(byte_width, 8);
                let bit_width = builder.ins().ireduce(types::I8, bit_width);

                builder
                    .ins()
                    .store(MemFlags::trusted(), bit_width, return_addr, 0);
            }
            ARRAY_DISCRIMINANT => {
                let array_info = self
                    .meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .array_info;
                let array_info = self.module.declare_data_in_func(array_info, builder.func);
                let array_info = builder.ins().symbol_value(self.pointer_ty, array_info);

                let ptr_size = self.pointer_ty.bytes();
                let second_field_offset =
                    ptr_size + layout::padding_needed_for(ptr_size, (32 / 8).min(8));

                let stride = second_field_offset + (32 / 8);

                let offset = build_offset(&mut builder, stride);
                let addr = builder.ins().iadd(array_info, offset);

                let size = builder
                    .ins()
                    .load(self.pointer_ty, MemFlags::trusted(), addr, 0);

                builder
                    .ins()
                    .store(MemFlags::trusted(), size, return_addr, 0);

                let ty = builder.ins().load(
                    self.pointer_ty,
                    MemFlags::trusted(),
                    addr,
                    second_field_offset as i32,
                );

                builder.ins().store(
                    MemFlags::trusted(),
                    ty,
                    return_addr,
                    second_field_offset as i32,
                );
            }
            SLICE_DISCRIMINANT => {
                let slice_info = self
                    .meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .slice_info;
                let slice_info = self.module.declare_data_in_func(slice_info, builder.func);
                let slice_info = builder.ins().symbol_value(self.pointer_ty, slice_info);

                let offset = build_offset(&mut builder, 32 / 8);
                let addr = builder.ins().iadd(slice_info, offset);

                let ty = builder.ins().load(types::I32, MemFlags::trusted(), addr, 0);

                builder.ins().store(MemFlags::trusted(), ty, return_addr, 0);
            }
            POINTER_DISCRIMINANT => {
                let pointer_info = self
                    .meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .pointer_info;
                let pointer_info = self.module.declare_data_in_func(pointer_info, builder.func);
                let pointer_info = builder.ins().symbol_value(self.pointer_ty, pointer_info);

                let offset = build_offset(&mut builder, 32 / 8);
                let addr = builder.ins().iadd(pointer_info, offset);

                let ty = builder.ins().load(types::I32, MemFlags::trusted(), addr, 0);

                builder.ins().store(MemFlags::trusted(), ty, return_addr, 0);
            }
            DISTINCT_DISCRIMINANT => {
                let distinct_info = self
                    .meta_tys
                    .info_arrays
                    .get_or_insert_with(|| MetaTyInfoArrays::new(self.module))
                    .distinct_info;
                let distinct_info = self
                    .module
                    .declare_data_in_func(distinct_info, builder.func);
                let distinct_info = builder.ins().symbol_value(self.pointer_ty, distinct_info);

                let offset = build_offset(&mut builder, 32 / 8);
                let addr = builder.ins().iadd(distinct_info, offset);

                let ty = builder.ins().load(types::I32, MemFlags::trusted(), addr, 0);

                builder.ins().store(MemFlags::trusted(), ty, return_addr, 0);
            }
            _ => unreachable!(),
        }

        builder.ins().return_(&[return_addr]);

        builder.switch_to_block(wrong_type_block);
        builder.seal_block(wrong_type_block);
        builder.set_cold_block(wrong_type_block);

        builder.ins().trap(TrapCode::User(1));

        builder.seal_all_blocks();
        builder.finalize();

        if self.verbosity == Verbosity::AllFunctions {
            println!(
                "get_{expected_disc}_info \x1B[90m{}\x1B[0m:\n{}",
                mangled_name, self.ctx.func
            );
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .unwrap_or_else(|err| {
                println!("Error defining function:");
                if let ModuleError::Compilation(CodegenError::Verifier(v)) = err {
                    println!("{}", v.to_string().replace("):", "):\n "));
                } else {
                    println!("{:?}", err);
                }
                std::process::exit(1);
            });

        self.module.clear_context(&mut self.ctx);
    }

    fn compile_real_function(
        &mut self,
        unmangled_name: &str,
        mangled_name: &str,
        module_name: hir::FileName,
        body: Idx<hir::Expr>,
        param_tys: Vec<Intern<Ty>>,
        return_ty: Intern<Ty>,
    ) -> FuncId {
        let (comp_sig, new_idx_to_old_idx) =
            (&param_tys, return_ty).to_final_signature(self.module, self.pointer_ty);
        let func_id = self
            .module
            .declare_function(mangled_name, Linkage::Export, &comp_sig)
            .unwrap();

        self.ctx.func.signature = comp_sig.clone();

        // Create the builder to build a function.
        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let function_compiler = FunctionCompiler {
            builder,
            file_name: module_name,
            mod_dir: self.mod_dir,
            signature: comp_sig,
            interner: self.interner,
            bodies_map: self.bodies_map,
            tys: self.tys,
            module: self.module,
            ptr_ty: self.pointer_ty,
            data_description: &mut self.data_description,
            functions_to_compile: &mut self.functions_to_compile,
            meta_tys: &mut self.meta_tys,
            local_functions: FxHashMap::default(),
            local_lambdas: FxHashMap::default(),
            functions: &mut self.functions,
            compiler_defined_functions: &mut self.compiler_defined_functions,
            globals: &mut self.data,
            str_id_gen: &mut self.str_id_gen,
            comptime_results: self.comptime_results,
            var_id_gen: UIDGenerator::default(),
            locals: FxHashMap::default(),
            params: FxHashMap::default(),
            exits: FxHashMap::default(),
            continues: FxHashMap::default(),
        };

        function_compiler.finish(param_tys, return_ty, body, new_idx_to_old_idx);

        if self.verbosity == Verbosity::AllFunctions
            || (self.verbosity == Verbosity::LocalFunctions
                && !module_name.is_mod(self.mod_dir, self.interner))
        {
            println!(
                "{} \x1B[90m{}\x1B[0m:\n{}",
                unmangled_name, mangled_name, self.ctx.func
            );
        }

        self.module
            .define_function(func_id, &mut self.ctx)
            .unwrap_or_else(|err| {
                println!("Error defining function:");
                if let ModuleError::Compilation(CodegenError::Verifier(v)) = err {
                    println!("{}", v.to_string().replace("):", "):\n "));
                } else {
                    println!("{:?}", err);
                }
                std::process::exit(1);
            });

        self.module.clear_context(&mut self.ctx);

        func_id
    }
}

#[allow(clippy::too_many_arguments)]
fn get_func_id(
    module: &mut dyn Module,
    pointer_ty: types::Type,
    mod_dir: &std::path::Path,
    functions: &mut FxHashMap<hir::Fqn, FuncId>,
    compiler_defined_functions: &mut FxHashMap<BuiltinFunction, FuncId>,
    functions_to_compile: &mut VecDeque<FunctionToCompile>,
    tys: &hir_ty::InferenceResult,
    bodies_map: &FxHashMap<hir::FileName, hir::Bodies>,
    interner: &Interner,
    fqn: hir::Fqn,
) -> FuncId {
    if let Some(func_id) = functions.get(&fqn) {
        return *func_id;
    }

    let (param_tys, return_ty) = tys[fqn]
        .0
        .as_function()
        .expect("tried to compile non-function as function");

    let global_body = bodies_map[&fqn.file].global_body(fqn.name);

    let lambda = match bodies_map[&fqn.file][global_body] {
        hir::Expr::Lambda(lambda) => lambda,
        _ => todo!("global with function type does not have a lambda as it's body"),
    };

    let is_extern = bodies_map[&fqn.file][lambda].is_extern;

    let ftc = FunctionToCompile {
        file_name: fqn.file,
        function_name: Some(fqn.name),
        lambda,
        param_tys: param_tys.clone(),
        return_ty,
    };

    if let Some(compiler_defined) = as_compiler_defined(is_extern, &ftc, mod_dir, interner) {
        if let Some(func_id) = compiler_defined_functions.get(&compiler_defined) {
            functions.insert(fqn, *func_id);

            return *func_id;
        }

        let (_, _, func_id) =
            compiler_defined.to_sig_and_func_id(module, pointer_ty, mod_dir, interner);

        functions_to_compile.push_back(ftc);

        compiler_defined_functions.insert(compiler_defined, func_id);
        functions.insert(fqn, func_id);

        return func_id;
    }

    functions_to_compile.push_back(ftc);

    let (comp_sig, _) = (&param_tys, return_ty).to_final_signature(module, pointer_ty);

    let func_id = if is_extern {
        module
            .declare_function(interner.lookup(fqn.name.0), Linkage::Import, &comp_sig)
            .expect("There are multiple extern functions with the same name")
    } else {
        module
            .declare_function(
                &fqn.to_mangled_name(mod_dir, interner),
                Linkage::Export,
                &comp_sig,
            )
            .unwrap()
    };

    functions.insert(fqn, func_id);

    func_id
}

fn cast(
    builder: &mut FunctionBuilder,
    val: Value,
    cast_from: Intern<Ty>,
    cast_to: Intern<Ty>,
) -> Value {
    if cast_from.is_functionally_equivalent_to(&cast_to, true) {
        return val;
    }

    if let (Ty::Array { size, .. }, Ty::Slice { .. }) = (cast_from.as_ref(), cast_to.as_ref()) {
        let slice_size = cast_to.size();

        // i don't really want to change this function's signature, so we can just get the
        // pointer type by dividing the slice by two since a slice is always gauranteed to be
        // two pointers
        let ptr_size = slice_size / 2;
        let ptr_ty = match ptr_size {
            1 => types::I8,
            2 => types::I16,
            4 => types::I32,
            8 => types::I64,
            16 => types::I128,
            _ => unreachable!(),
        };

        let slice_stack_slot = builder.create_sized_stack_slot(StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: slice_size,
        });

        let len = builder.ins().iconst(ptr_ty, *size as i64);
        builder.ins().stack_store(len, slice_stack_slot, 0);

        builder
            .ins()
            .stack_store(val, slice_stack_slot, ptr_size as i32);

        return builder.ins().stack_addr(ptr_ty, slice_stack_slot, 0);
    }
    if let (Ty::Slice { .. }, Ty::Array { .. }) = (cast_from.as_ref(), cast_to.as_ref()) {
        let slice_size = cast_from.size();

        let ptr_size = slice_size / 2;
        let ptr_ty = match ptr_size {
            1 => types::I8,
            2 => types::I16,
            4 => types::I32,
            8 => types::I64,
            16 => types::I128,
            _ => unreachable!(),
        };

        // todo: do a runtime check that the lengths match

        return builder
            .ins()
            .load(ptr_ty, MemFlags::trusted(), val, ptr_size as i32);
    }

    match (cast_from.get_final_ty(), cast_to.get_final_ty()) {
        (FinalTy::Number(cast_from), FinalTy::Number(cast_to)) => {
            cast_num(builder, val, cast_from, cast_to)
        }
        _ => val,
    }
}

fn cast_ty_to_cranelift(
    builder: &mut FunctionBuilder,
    val: Value,
    cast_from: Intern<Ty>,
    cast_to: types::Type,
) -> Value {
    if let FinalTy::Number(cast_from) = cast_from.get_final_ty() {
        cast_num(
            builder,
            val,
            cast_from,
            NumberType {
                ty: cast_to,
                float: false,
                signed: false,
            },
        )
    } else {
        val
    }
}

fn cast_num(
    builder: &mut FunctionBuilder,
    val: Value,
    cast_from: NumberType,
    cast_to: NumberType,
) -> Value {
    if cast_from.bit_width() == cast_to.bit_width() && cast_from.float == cast_to.float {
        // the cast is irrelevant, so just return the value
        return val;
    }

    match (cast_from.float, cast_to.float) {
        (true, true) => {
            // float to float
            match cast_from.bit_width().cmp(&cast_to.bit_width()) {
                std::cmp::Ordering::Less => builder.ins().fpromote(cast_to.ty, val),
                std::cmp::Ordering::Equal => val,
                std::cmp::Ordering::Greater => builder.ins().fdemote(cast_to.ty, val),
            }
        }
        (true, false) => {
            // float to int

            // cranelift can only convert floats to i32 or i64, so we do that first,
            // then cast the i32 or i64 to the actual one we want
            let int_to = match cast_from.bit_width() {
                32 => types::I32,
                64 => types::I64,
                _ => unreachable!(),
            };

            let first_cast = if cast_to.signed {
                builder.ins().fcvt_to_sint_sat(int_to, val)
            } else {
                builder.ins().fcvt_to_uint_sat(int_to, val)
            };

            // now we can convert the `first_cast` int value to the actual int type we want
            match cast_from.bit_width().cmp(&cast_to.bit_width()) {
                std::cmp::Ordering::Less if cast_to.signed => {
                    builder.ins().sextend(cast_to.ty, first_cast)
                }
                std::cmp::Ordering::Less => builder.ins().uextend(cast_to.ty, first_cast),
                std::cmp::Ordering::Equal => first_cast,
                std::cmp::Ordering::Greater => builder.ins().ireduce(cast_to.ty, first_cast),
            }
        }
        (false, true) => {
            // int to float

            // first we have to convert the int to an int that can converted to float
            let int_to = match cast_to.bit_width() {
                32 => types::I32,
                64 => types::I64,
                _ => unreachable!(),
            };

            let first_cast = match cast_from.bit_width().cmp(&cast_to.bit_width()) {
                std::cmp::Ordering::Less if cast_from.signed && cast_to.signed => {
                    builder.ins().sextend(int_to, val)
                }
                std::cmp::Ordering::Less => builder.ins().uextend(int_to, val),
                std::cmp::Ordering::Equal => val,
                std::cmp::Ordering::Greater => builder.ins().ireduce(int_to, val),
            };

            // now we can convert that 32 or 64 bit int into a 32 or 64 bit float
            if cast_from.signed {
                builder.ins().fcvt_from_sint(cast_to.ty, first_cast)
            } else {
                builder.ins().fcvt_from_uint(cast_to.ty, first_cast)
            }
        }
        (false, false) => {
            // int to int
            match cast_from.bit_width().cmp(&cast_to.bit_width()) {
                std::cmp::Ordering::Less if cast_from.signed && cast_to.signed => {
                    builder.ins().sextend(cast_to.ty, val)
                }
                std::cmp::Ordering::Less => builder.ins().uextend(cast_to.ty, val),
                std::cmp::Ordering::Equal => val,
                std::cmp::Ordering::Greater => builder.ins().ireduce(cast_to.ty, val),
            }
        }
    }
}

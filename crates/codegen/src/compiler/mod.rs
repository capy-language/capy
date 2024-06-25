pub mod comptime;
pub mod functions;
pub mod program;

use cranelift::codegen::ir::StackSlot;
use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{
    types, FunctionBuilder, FunctionBuilderContext, InstBuilder, MemFlags, StackSlotData,
    StackSlotKind, Value,
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir::FQComptime;
use hir_ty::{ComptimeResult, InternTyExt, Ty};
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::builtin::{as_compiler_defined_func, BuiltinFunction};
use crate::extend::ExtendWithNumBytes;
use crate::layout::{self, GetLayoutInfo};
use crate::mangle::{self, Mangle};
use crate::{
    convert::{self, *},
    FinalSignature, Verbosity,
};

use self::abi::Abi;
use self::functions::FunctionCompiler;

#[cfg(not(debug_assertions))]
use std::hint::unreachable_unchecked;

macro_rules! unreachable_opt_on_release {
    () => {{
        #[cfg(debug_assertions)]
        panic!();
        #[cfg(not(debug_assertions))]
        unsafe {
            unreachable_unchecked()
        }
    }};
}

#[derive(Default)]
pub(crate) struct MetaTyData {
    pub(crate) tys_to_compile: Vec<Intern<Ty>>,

    pub(crate) array_uid_gen: UIDGenerator,
    pub(crate) slice_uid_gen: UIDGenerator,
    pub(crate) pointer_uid_gen: UIDGenerator,
    pub(crate) distinct_uid_gen: UIDGenerator,
    pub(crate) function_uid_gen: UIDGenerator,
    pub(crate) struct_uid_gen: UIDGenerator,

    pub(crate) layout_arrays: Option<MetaTyLayoutArrays>,
    pub(crate) info_arrays: Option<MetaTyInfoArrays>,
}

pub(crate) struct MetaTyLayoutArrays {
    pub(crate) array_layout_array: DataId,
    pub(crate) distinct_layout_array: DataId,
    pub(crate) struct_layout_array: DataId,

    pub(crate) array_layout_slice: DataId,
    pub(crate) distinct_layout_slice: DataId,
    pub(crate) struct_layout_slice: DataId,
    pub(crate) pointer_layout: DataId,
}

impl MetaTyLayoutArrays {
    pub(crate) fn new(module: &mut dyn Module) -> Self {
        let mut declare = |name: &str| {
            module
                .declare_data(
                    &mangle::mangle_internal(name),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data")
        };

        Self {
            array_layout_array: declare("array_layout_array"),
            array_layout_slice: declare("array_layout_slice"),
            distinct_layout_array: declare("distinct_layout_array"),
            distinct_layout_slice: declare("distinct_layout_slice"),
            struct_layout_array: declare("struct_layout_array"),
            struct_layout_slice: declare("struct_layout_slice"),
            pointer_layout: declare("pointer_layout"),
        }
    }
}

pub(crate) struct MetaTyInfoArrays {
    // the actual raw type info arrays
    pub(crate) array_info_array: DataId,
    pub(crate) slice_info_array: DataId,
    pub(crate) pointer_info_array: DataId,
    pub(crate) distinct_info_array: DataId,
    pub(crate) struct_info_array: DataId,

    // the global slices available in "meta.capy"
    pub(crate) array_info_slice: DataId,
    pub(crate) slice_info_slice: DataId,
    pub(crate) pointer_info_slice: DataId,
    pub(crate) distinct_info_slice: DataId,
    pub(crate) struct_info_slice: DataId,
}

impl MetaTyInfoArrays {
    pub(crate) fn new(module: &mut dyn Module) -> Self {
        let mut declare = |name: &str| {
            module
                .declare_data(
                    &mangle::mangle_internal(name),
                    Linkage::Export,
                    false,
                    false,
                )
                .expect("error declaring data")
        };

        Self {
            array_info_array: declare("array_info_array"),
            array_info_slice: declare("array_info_slice"),
            slice_info_array: declare("slice_info_array"),
            slice_info_slice: declare("slice_info_slice"),
            pointer_info_array: declare("pointer_info_array"),
            pointer_info_slice: declare("pointer_info_slice"),
            distinct_info_array: declare("distinct_info_array"),
            distinct_info_slice: declare("distinct_info_slice"),
            struct_info_array: declare("struct_info_array"),
            struct_info_slice: declare("struct_info_slice"),
        }
    }
}

pub(crate) struct ComptimeData {
    pub(crate) init_flag: DataId,
    pub(crate) value: DataId,
}

impl ComptimeData {
    pub(crate) fn new(
        module: &mut dyn Module,
        mod_dir: &std::path::Path,
        interner: &Interner,
        comptime: FQComptime,
    ) -> Self {
        let mut declare = |name: &str| {
            module
                .declare_data(
                    &(comptime, name).to_mangled_name(mod_dir, interner),
                    Linkage::Export,
                    true,
                    false,
                )
                .expect("error declaring data")
        };

        Self {
            init_flag: declare("init_flag"),
            value: declare("value"),
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
    pub(crate) final_binary: bool,
    pub(crate) verbosity: Verbosity,

    pub(crate) mod_dir: &'a std::path::Path,

    pub(crate) interner: &'a Interner,
    pub(crate) world_bodies: &'a hir::WorldBodies,
    pub(crate) tys: &'a hir_ty::ProjectInference,

    pub(crate) builder_context: FunctionBuilderContext,
    pub(crate) ctx: codegen::Context,
    pub(crate) data_desc: DataDescription,
    pub(crate) module: &'a mut dyn Module,
    pub(crate) ptr_ty: types::Type,

    // bodies to compile
    pub(crate) functions_to_compile: VecDeque<FunctionToCompile>,

    // globals
    pub(crate) functions: FxHashMap<hir::Fqn, FuncId>,
    pub(crate) compiler_defined_functions: FxHashMap<BuiltinFunction, FuncId>,
    pub(crate) data: FxHashMap<hir::Fqn, DataId>,
    pub(crate) meta_tys: MetaTyData,
    pub(crate) str_id_gen: UIDGenerator,
    pub(crate) i128_id_gen: UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<FQComptime, ComptimeResult>,
    pub(crate) comptime_data: FxHashMap<FQComptime, ComptimeData>,

    pub(crate) default_abi: Abi,
}

impl Compiler<'_> {
    fn finalize_tys(&mut self) {
        layout::calc_layouts(self.tys.all_tys(), self.ptr_ty.bits());
        convert::calc_finals(self.tys.all_tys(), self.ptr_ty);
    }

    fn compile_queued(&mut self) {
        while let Some(ftc) = self.functions_to_compile.pop_front() {
            self.compile_ftc(ftc);
        }

        let mut array_count = 0;
        let mut slice_count = 0;
        let mut pointer_count = 0;
        let mut distinct_count = 0;
        let mut struct_count = 0;

        let mut array_mem_data = Vec::new();
        let mut distinct_mem_data = Vec::new();
        let mut struct_mem_data = Vec::new();

        let mut array_info_data = Vec::new();
        let mut slice_info_data = Vec::new();
        let mut pointer_info_data = Vec::new();
        let mut distinct_info_data = Vec::new();

        let mut struct_infos_to_compile = Vec::new();

        for ty in &self.meta_tys.tys_to_compile {
            match ty.as_ref() {
                Ty::Array { .. } => {
                    array_count += 1;
                }
                Ty::Slice { .. } => {
                    slice_count += 1;
                }
                Ty::Pointer { .. } => {
                    pointer_count += 1;
                }
                Ty::Distinct { .. } => {
                    distinct_count += 1;
                }
                Ty::Struct { .. } => {
                    struct_count += 1;
                }
                _ => {}
            }

            'mem: {
                if self.meta_tys.layout_arrays.is_some() {
                    let data = match ty.as_ref() {
                        Ty::Array { .. } => &mut array_mem_data,
                        Ty::Distinct { .. } => &mut distinct_mem_data,
                        Ty::Struct { .. } => &mut struct_mem_data,
                        _ => break 'mem,
                    };

                    let size = ty.size();
                    let align = ty.align();

                    data.extend_with_num_bytes(
                        size,
                        self.ptr_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                    data.extend_with_num_bytes(
                        align,
                        self.ptr_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                }
            }

            if self.meta_tys.info_arrays.is_some() {
                match ty.as_ref() {
                    Ty::Array { size, sub_ty, .. } => {
                        array_info_data.extend_with_num_bytes(
                            (*size) as u32,
                            self.ptr_ty.bits() as u8,
                            self.module.isa().endianness(),
                        );

                        let padding = layout::padding_needed_for(
                            array_info_data.len() as u32,
                            (32 / 8).min(8),
                        );
                        array_info_data.extend(std::iter::repeat(0).take(padding as usize));

                        array_info_data.extend_with_num_bytes(
                            sub_ty.to_previous_type_id(&self.meta_tys, self.ptr_ty),
                            32,
                            self.module.isa().endianness(),
                        );

                        let ptr_size = self.ptr_ty.bytes();
                        let padding = layout::padding_needed_for(
                            array_info_data.len() as u32,
                            ptr_size.min(8),
                        );
                        array_info_data.extend(std::iter::repeat(0).take(padding as usize));
                    }
                    Ty::Slice { sub_ty } => {
                        slice_info_data.extend_with_num_bytes(
                            sub_ty.to_previous_type_id(&self.meta_tys, self.ptr_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Pointer { sub_ty, .. } => {
                        pointer_info_data.extend_with_num_bytes(
                            sub_ty.to_previous_type_id(&self.meta_tys, self.ptr_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Distinct { sub_ty: ty, .. } => {
                        distinct_info_data.extend_with_num_bytes(
                            ty.to_previous_type_id(&self.meta_tys, self.ptr_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Struct { .. } => {
                        struct_infos_to_compile.push(ty);
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
            align: u64,
        ) {
            data_desc.define(bytes.into_boxed_slice());
            data_desc.set_align(align);
            module
                .define_data(info_array, data_desc)
                .expect("error defining data");
            data_desc.clear();
        }

        fn define_with_relocs(
            module: &mut dyn Module,
            data_desc: &mut DataDescription,
            info_array: DataId,
            bytes: Vec<u8>,
            align: u64,
            relocs: Vec<(u32, DataId)>,
        ) {
            data_desc.define(bytes.into_boxed_slice());
            data_desc.set_align(align);

            for (offset, id) in relocs {
                let local = module.declare_data_in_data(id, data_desc);

                data_desc.write_data_addr(offset, local, 0);
            }

            module
                .define_data(info_array, data_desc)
                .expect("error defining data");

            data_desc.clear();
        }

        fn define_slice(
            module: &mut dyn Module,
            data_desc: &mut DataDescription,
            info_array: DataId,
            len: u32,
            ptr: DataId,
        ) {
            let mut bytes = Vec::with_capacity(module.target_config().pointer_bytes() as usize);
            bytes.extend_with_num_bytes(
                len,
                module.target_config().pointer_bits(),
                module.isa().endianness(),
            );
            // zeroed-out pointer, this will be written over later
            bytes
                .extend(std::iter::repeat(0).take(module.target_config().pointer_bytes() as usize));

            data_desc.define(bytes.into_boxed_slice());
            data_desc.set_align(module.target_config().pointer_bytes().min(8) as u64);

            let local = module.declare_data_in_data(ptr, data_desc);

            data_desc.write_data_addr(module.target_config().pointer_bytes() as u32, local, 0);

            module
                .define_data(info_array, data_desc)
                .expect("error defining data");

            data_desc.clear();
        }

        let ptr_align = self.ptr_ty.bytes().min(8) as u64;
        let meta_type_align = 4;

        if let Some(mem_arrays) = &self.meta_tys.layout_arrays {
            define(
                self.module,
                &mut self.data_desc,
                mem_arrays.array_layout_array,
                array_mem_data,
                ptr_align,
            );
            define(
                self.module,
                &mut self.data_desc,
                mem_arrays.distinct_layout_array,
                distinct_mem_data,
                ptr_align,
            );
            define(
                self.module,
                &mut self.data_desc,
                mem_arrays.struct_layout_array,
                struct_mem_data,
                ptr_align,
            );

            define_slice(
                self.module,
                &mut self.data_desc,
                mem_arrays.array_layout_slice,
                array_count,
                mem_arrays.array_layout_array,
            );
            define_slice(
                self.module,
                &mut self.data_desc,
                mem_arrays.distinct_layout_slice,
                distinct_count,
                mem_arrays.distinct_layout_array,
            );
            define_slice(
                self.module,
                &mut self.data_desc,
                mem_arrays.struct_layout_slice,
                struct_count,
                mem_arrays.struct_layout_array,
            );

            // pointer layout

            let mut pointer_layout_data = Vec::with_capacity(self.ptr_ty.bytes() as usize * 2);
            pointer_layout_data.extend_with_num_bytes(
                self.ptr_ty.bytes(),
                self.ptr_ty.bits() as u8,
                self.module.isa().endianness(),
            );
            pointer_layout_data.extend_with_num_bytes(
                self.ptr_ty.bytes().min(8),
                self.ptr_ty.bits() as u8,
                self.module.isa().endianness(),
            );
            define(
                self.module,
                &mut self.data_desc,
                mem_arrays.pointer_layout,
                pointer_layout_data,
                ptr_align,
            );
        }
        if let Some(info_arrays) = &self.meta_tys.info_arrays {
            define(
                self.module,
                &mut self.data_desc,
                info_arrays.array_info_array,
                array_info_data,
                ptr_align.max(meta_type_align),
            );
            define(
                self.module,
                &mut self.data_desc,
                info_arrays.slice_info_array,
                slice_info_data,
                ptr_align, // the alignment of a slice is the alignment of a pointer
            );
            define(
                self.module,
                &mut self.data_desc,
                info_arrays.pointer_info_array,
                pointer_info_data,
                meta_type_align,
            );
            define(
                self.module,
                &mut self.data_desc,
                info_arrays.distinct_info_array,
                distinct_info_data,
                meta_type_align,
            );

            define_slice(
                self.module,
                &mut self.data_desc,
                info_arrays.array_info_slice,
                array_count,
                info_arrays.array_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_desc,
                info_arrays.slice_info_slice,
                slice_count,
                info_arrays.slice_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_desc,
                info_arrays.pointer_info_slice,
                pointer_count,
                info_arrays.pointer_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_desc,
                info_arrays.distinct_info_slice,
                distinct_count,
                info_arrays.distinct_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_desc,
                info_arrays.struct_info_slice,
                struct_count,
                info_arrays.struct_info_array,
            );

            // now building the arrays of every struct member in the program

            fn declare(module: &mut dyn Module, name: &str) -> DataId {
                module
                    .declare_data(name, Linkage::Local, true, false)
                    .expect("error declaring data")
            }

            let mut member_array_starting_offsets = Vec::new();

            let mut member_name_str_uid_gen = UIDGenerator::default();
            let mut member_array_data = Vec::new();
            let mut member_array_relocs = Vec::new();

            for s in &struct_infos_to_compile {
                let Ty::Struct { members, .. } = s.as_ref() else {
                    unreachable_opt_on_release!();
                };

                let member_offsets = s.struct_layout().unwrap();
                let member_offsets = member_offsets.offsets();

                member_array_starting_offsets.push(member_array_data.len());

                for (idx, (name, ty)) in members.iter().enumerate() {
                    // padding for next usize (str)
                    let padding = layout::padding_needed_for(
                        member_array_data.len() as u32,
                        self.ptr_ty.bytes().min(8),
                    );
                    member_array_data.extend(std::iter::repeat(0).take(padding as usize));

                    // name field

                    let name_offset = member_array_data.len();

                    // zeroed-out str pointer, this will be written over later
                    member_array_data
                        .extend(std::iter::repeat(0).take(self.ptr_ty.bytes() as usize));

                    let mut name_str_bytes = self.interner.lookup(name.0).as_bytes().to_vec();
                    name_str_bytes.push(0);
                    let name_str_id = declare(
                        self.module,
                        &format!(
                            ".member_str{}",
                            member_name_str_uid_gen.generate_unique_id()
                        ),
                    );
                    define(
                        self.module,
                        &mut self.data_desc,
                        name_str_id,
                        name_str_bytes,
                        1,
                    );

                    member_array_relocs.push((name_offset as u32, name_str_id));

                    // padding for next u32 (type)

                    let padding =
                        layout::padding_needed_for(member_array_data.len() as u32, (32 / 8).min(8));
                    member_array_data.extend(std::iter::repeat(0).take(padding as usize));

                    // ty field

                    member_array_data.extend_with_num_bytes(
                        ty.to_previous_type_id(&self.meta_tys, self.ptr_ty),
                        32,
                        self.module.isa().endianness(),
                    );

                    // padding for next usize

                    let padding = layout::padding_needed_for(
                        member_array_data.len() as u32,
                        self.ptr_ty.bytes().min(8),
                    );
                    member_array_data.extend(std::iter::repeat(0).take(padding as usize));

                    // offset field

                    member_array_data.extend_with_num_bytes(
                        member_offsets[idx],
                        self.ptr_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                }
            }

            // now that all the strings have been created, declare the member info array, and insert
            // the relocations.

            let member_array_id =
                declare(self.module, &mangle::mangle_internal("struct_member_info"));

            define_with_relocs(
                self.module,
                &mut self.data_desc,
                member_array_id,
                member_array_data,
                meta_type_align.max(ptr_align),
                member_array_relocs,
            );

            // now that all the members have been defined, we can assemble the actual struct info array

            let member_array_local = self
                .module
                .declare_data_in_data(member_array_id, &mut self.data_desc);

            let mut struct_array_data = Vec::new();

            for (idx, s) in struct_infos_to_compile.iter().enumerate() {
                let Ty::Struct { members, .. } = s.as_ref() else {
                    unreachable_opt_on_release!();
                };
                let members_len = members.len();

                struct_array_data.extend_with_num_bytes(
                    members_len as u32,
                    self.ptr_ty.bits() as u8,
                    self.module.isa().endianness(),
                );

                let ptr_member_offset = struct_array_data.len();

                struct_array_data.extend_with_num_bytes(
                    0,
                    self.ptr_ty.bits() as u8,
                    self.module.isa().endianness(),
                );

                let member_array_starting_offset = member_array_starting_offsets[idx];

                self.data_desc.write_data_addr(
                    ptr_member_offset as u32,
                    member_array_local,
                    member_array_starting_offset as i64,
                );
            }

            define(
                self.module,
                &mut self.data_desc,
                info_arrays.struct_info_array,
                struct_array_data,
                ptr_align, // the alignment of a slice == the alignment of a single pointer
            );
        }
    }

    fn get_func_id(&mut self, fqn: hir::Fqn) -> FuncId {
        get_func_id(
            self.module,
            self.ptr_ty,
            self.mod_dir,
            &mut self.functions,
            &mut self.compiler_defined_functions,
            &mut self.functions_to_compile,
            self.tys,
            self.world_bodies,
            self.interner,
            fqn,
        )
    }

    fn compile_ftc(&mut self, ftc: FunctionToCompile) {
        let hir::Lambda {
            body, is_extern, ..
        } = &self.world_bodies[ftc.file_name][ftc.lambda];

        if let Some(compiler_defined) =
            as_compiler_defined_func(*is_extern, &ftc, self.mod_dir, self.interner)
        {
            let (mangled, sig, func_id) = compiler_defined.to_sig_and_func_id(
                self.module,
                self.ptr_ty,
                self.mod_dir,
                self.interner,
            );

            match compiler_defined {
                BuiltinFunction::PtrBitcast => {
                    self.compile_bitcast_fn("ptr_bitcast", &mangled, sig, func_id, self.ptr_ty)
                }
                BuiltinFunction::I32Bitcast => {
                    self.compile_bitcast_fn("i32_bitcast", &mangled, sig, func_id, types::I32)
                }
            }
            return;
        }

        if *is_extern {
            unreachable!("regular extern functions should not be pushed to `functions_to_compile`");
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

    fn compile_bitcast_fn(
        &mut self,
        unmangled_name: &str,
        mangled_name: &str,
        sig: FinalSignature,
        func_id: FuncId,
        ty: types::Type,
    ) {
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
        let arg_ptr = builder.append_block_param(entry_block, ty);
        builder.ins().return_(&[arg_ptr]);

        builder.seal_all_blocks();
        builder.finalize();

        if self.verbosity == Verbosity::AllFunctions {
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
        let fn_abi = self.default_abi.fn_to_target((&param_tys, return_ty));
        let comp_sig = fn_abi.to_cl(self.ptr_ty);
        let func_id = self
            .module
            .declare_function(mangled_name, Linkage::Export, &comp_sig)
            .unwrap();

        self.ctx.func.signature = comp_sig.clone();

        // Create the builder to build a function.
        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let function_compiler = FunctionCompiler {
            final_binary: self.final_binary,
            builder,
            file_name: module_name,
            mod_dir: self.mod_dir,
            interner: self.interner,
            world_bodies: self.world_bodies,
            tys: self.tys,
            module: self.module,
            ptr_ty: self.ptr_ty,
            data_description: &mut self.data_desc,
            functions_to_compile: &mut self.functions_to_compile,
            meta_tys: &mut self.meta_tys,
            local_functions: FxHashMap::default(),
            local_lambdas: FxHashMap::default(),
            functions: &mut self.functions,
            compiler_defined_functions: &mut self.compiler_defined_functions,
            globals: &mut self.data,
            str_id_gen: &mut self.str_id_gen,
            i128_id_gen: &mut self.i128_id_gen,
            comptime_results: self.comptime_results,
            comptime_data: &mut self.comptime_data,
            var_id_gen: UIDGenerator::default(),
            locals: FxHashMap::default(),
            params: FxHashMap::default(),
            exits: FxHashMap::default(),
            continues: FxHashMap::default(),
            defer_stack: Vec::new(),
        };

        let debug_print = self.verbosity == Verbosity::AllFunctions
            || (self.verbosity == Verbosity::LocalFunctions
                && !module_name.is_mod(self.mod_dir, self.interner));

        if debug_print {
            println!("{} \x1B[90m{}\x1B[0m:", unmangled_name, mangled_name);
        }

        function_compiler.finish(fn_abi, (&param_tys, return_ty), body, debug_print);

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
    tys: &hir_ty::ProjectInference,
    world_bodies: &hir::WorldBodies,
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

    if world_bodies.is_extern(fqn) {
        let comp_sig = Into::<Abi>::into(module.target_config())
            .fn_to_target((&param_tys, return_ty))
            .to_cl(pointer_ty);

        let func_id = module
            .declare_function(interner.lookup(fqn.name.0), Linkage::Import, &comp_sig)
            .expect("There are multiple extern functions with the same name");

        functions.insert(fqn, func_id);

        return func_id;
    }

    let global_body = world_bodies.body(fqn);

    let lambda = match world_bodies[fqn.file][global_body] {
        hir::Expr::Lambda(lambda) => lambda,
        hir::Expr::LocalGlobal(global) => {
            let fqn = hir::Fqn {
                file: fqn.file,
                name: global.name,
            };

            // todo: remove recursion
            return get_func_id(
                module,
                pointer_ty,
                mod_dir,
                functions,
                compiler_defined_functions,
                functions_to_compile,
                tys,
                world_bodies,
                interner,
                fqn,
            );
        }
        hir::Expr::Member { previous, field } => {
            if let Ty::File(file) = tys[fqn.file][previous].as_ref() {
                let fqn = hir::Fqn {
                    file: *file,
                    name: field.name,
                };

                // todo: remove recursion
                return get_func_id(
                    module,
                    pointer_ty,
                    mod_dir,
                    functions,
                    compiler_defined_functions,
                    functions_to_compile,
                    tys,
                    world_bodies,
                    interner,
                    fqn,
                );
            } else {
                unreachable!("there shouldn't be any other possibilities here");
            }
        }
        _ => todo!("global with function type does not have a lambda as it's body"),
    };

    let is_extern = world_bodies[fqn.file][lambda].is_extern;

    let ftc = FunctionToCompile {
        file_name: fqn.file,
        function_name: Some(fqn.name),
        lambda,
        param_tys: param_tys.clone(),
        return_ty,
    };

    if let Some(compiler_defined) = as_compiler_defined_func(is_extern, &ftc, mod_dir, interner) {
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

    if is_extern {
        let comp_sig = Into::<Abi>::into(module.target_config())
            .fn_to_target((&param_tys, return_ty))
            .to_cl(pointer_ty);

        let func_id = module
            .declare_function(interner.lookup(fqn.name.0), Linkage::Import, &comp_sig)
            .expect("There are multiple extern functions with the same name");

        functions.insert(fqn, func_id);

        return func_id;
    }

    functions_to_compile.push_back(ftc);

    let comp_sig = Into::<Abi>::into(module.target_config())
        .fn_to_target((&param_tys, return_ty))
        .to_cl(pointer_ty);

    let func_id = module
        .declare_function(
            &fqn.to_mangled_name(mod_dir, interner),
            Linkage::Export,
            &comp_sig,
        )
        .unwrap();

    functions.insert(fqn, func_id);

    func_id
}

#[derive(Debug, Clone, Copy)]
enum Location {
    Stack(StackSlot),
    Addr(Value),
}

#[derive(Debug, Clone, Copy)]
pub struct MemoryLoc {
    addr: Location,
    offset: u32,
}

impl MemoryLoc {
    pub fn from_stack(stack_slot: StackSlot, offset: u32) -> MemoryLoc {
        MemoryLoc {
            addr: Location::Stack(stack_slot),
            offset,
        }
    }

    pub fn from_addr(addr: Value, offset: u32) -> MemoryLoc {
        MemoryLoc {
            addr: Location::Addr(addr),
            offset,
        }
    }

    fn with_offset(self, offset: u32) -> MemoryLoc {
        MemoryLoc {
            addr: self.addr,
            offset: self.offset + offset,
        }
    }

    /// This converts the address + offset into a single address if needed
    fn into_value(self, builder: &mut FunctionBuilder, ptr_ty: types::Type) -> Value {
        match self.addr {
            Location::Stack(slot) => builder.ins().stack_addr(ptr_ty, slot, self.offset as i32),
            Location::Addr(addr) => {
                if self.offset > 0 {
                    builder.ins().iadd_imm(addr, self.offset as i64)
                } else {
                    addr
                }
            }
        }
    }

    fn store(&self, builder: &mut FunctionBuilder, x: Value, offset: i32) {
        match self.addr {
            Location::Stack(slot) => {
                builder
                    .ins()
                    .stack_store(x, slot, offset + self.offset as i32)
            }
            Location::Addr(addr) => {
                builder
                    .ins()
                    .store(MemFlags::trusted(), x, addr, offset + self.offset as i32)
            }
        };
    }

    /// Does a simple store of a memmove if necessary
    ///
    /// By using this function, you promise that the bytes of val can fit inside
    /// the given MemoryLoc.
    ///
    /// You also promise that the alignment of val matches the alignment of the
    /// the given MemoryLoc.
    fn write(
        self,
        val: Option<Value>,
        ty: Intern<Ty>,
        module: &mut dyn Module,
        builder: &mut FunctionBuilder,
    ) {
        let Some(val) = val else {
            return;
        };

        if ty.is_aggregate() {
            match self.addr {
                Location::Addr(addr) => {
                    let addr = builder.ins().iadd_imm(addr, self.offset as i64);
                    builder.emit_small_memory_copy(
                        module.target_config(),
                        addr,
                        val,
                        // this has to be stride for some reason, it can't be size
                        ty.stride() as u64,
                        ty.align() as u8,
                        ty.align() as u8,
                        true,
                        MemFlags::trusted(),
                    )
                }
                Location::Stack(slot) => {
                    // be very explicit to cranelift what we are doing here
                    // since there is no `emit_stack_memcpy`, do it ourselves
                    let mut off = 0;
                    macro_rules! mem_cpy_loop {
                        ($width:expr) => {
                            while (off + $width) <= (ty.stride() as i32 / $width) * $width {
                                let bytes = builder.ins().load(
                                    cranelift::codegen::ir::Type::int_with_byte_size($width)
                                        .unwrap(),
                                    MemFlags::trusted(),
                                    val,
                                    off,
                                );
                                builder
                                    .ins()
                                    .stack_store(bytes, slot, off + self.offset as i32);
                                off += $width;
                            }
                        };
                    }
                    mem_cpy_loop!(8);
                    mem_cpy_loop!(4);
                    mem_cpy_loop!(2);
                    mem_cpy_loop!(1);
                }
            }
        } else {
            match self.addr {
                Location::Stack(slot) => builder.ins().stack_store(val, slot, self.offset as i32),
                Location::Addr(addr) => {
                    builder
                        .ins()
                        .store(MemFlags::trusted(), val, addr, self.offset as i32)
                }
            };
        }
    }
}

trait UnwrapOrAlloca {
    fn unwrap_or_alloca(self, builder: &mut FunctionBuilder, ty: Intern<Ty>) -> MemoryLoc;
}

impl UnwrapOrAlloca for Option<MemoryLoc> {
    fn unwrap_or_alloca(self, builder: &mut FunctionBuilder, ty: Intern<Ty>) -> MemoryLoc {
        match self {
            Some(mem) => mem,
            None => {
                let stack_slot = builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: ty.size(),
                    align_shift: ty.align() as u8,
                });

                MemoryLoc::from_stack(stack_slot, 0)
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_into_memory(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    ptr_ty: types::Type,
    val: Option<Value>,
    cast_from: Intern<Ty>,
    cast_to: Intern<Ty>,
    memory: Option<MemoryLoc>,
) -> Option<Value> {
    if cast_from.is_functionally_equivalent_to(&cast_to, true) {
        match memory {
            Some(memory) => {
                assert_eq!(cast_from.align(), cast_to.align());

                memory.write(val, cast_to, module, builder);

                return Some(memory.into_value(builder, ptr_ty));
            }
            None => return val,
        }
    }

    let cast_from = cast_from.remove_distinct();
    let cast_to = cast_to.remove_distinct();

    match (cast_from.as_ref(), cast_to.as_ref()) {
        (Ty::Array { size, .. }, Ty::Slice { .. }) => {
            let memory = memory.unwrap_or_alloca(builder, cast_to);

            let len = builder.ins().iconst(ptr_ty, *size as i64);
            memory.store(builder, len, 0 as i32);
            memory.store(builder, val?, ptr_ty.bytes() as i32);

            return Some(memory.into_value(builder, ptr_ty));
        }
        (Ty::Slice { .. }, Ty::Array { .. }) => {
            // todo: do a runtime check that the lengths match

            return Some(builder.ins().load(
                ptr_ty,
                MemFlags::trusted(),
                val?,
                // the second field (after usize len) is the addr of the array
                ptr_ty.bytes() as i32,
            ));
        }
        _ if cast_to.is_any_struct() => {
            let any_mem = memory.unwrap_or_alloca(builder, cast_to);

            let struct_layout = cast_to.struct_layout().unwrap();

            for (idx, (_, ty)) in cast_to.as_struct().unwrap().into_iter().enumerate() {
                match ty.as_ref() {
                    Ty::Pointer { .. } => {
                        if let Some(val) = val {
                            let offset = struct_layout.offsets()[idx] as i32;

                            let ptr = if cast_from.is_aggregate() {
                                val
                            } else {
                                let tmp_stack_slot =
                                    builder.create_sized_stack_slot(StackSlotData {
                                        kind: StackSlotKind::ExplicitSlot,
                                        size: cast_from.size(),
                                        align_shift: cast_from.align() as u8,
                                    });

                                builder.ins().stack_store(val, tmp_stack_slot, 0);

                                builder.ins().stack_addr(ptr_ty, tmp_stack_slot, 0)
                            };

                            any_mem.store(builder, ptr, offset);
                        }
                    }
                    Ty::Type => {
                        let offset = struct_layout.offsets()[idx] as i32;

                        let id = cast_from.to_type_id(meta_tys, ptr_ty) as i64;
                        let id = builder.ins().iconst(types::I32, id);

                        any_mem.store(builder, id, offset);
                    }
                    _ => {}
                }
            }

            return Some(any_mem.into_value(builder, ptr_ty));
        }
        (Ty::Struct { .. }, Ty::Struct { .. }) => {
            return cast_struct_to_struct(
                meta_tys, module, builder, ptr_ty, val, cast_from, cast_to, memory,
            );
        }
        (Ty::Array { .. }, Ty::Array { .. }) => {
            return cast_array_to_array(
                meta_tys, module, builder, ptr_ty, val, cast_from, cast_to, memory,
            );
        }
        _ => {}
    }

    // it's a simple cast

    let val = match (cast_from.get_final_ty(), cast_to.get_final_ty()) {
        (FinalTy::Number(cast_from), FinalTy::Number(cast_to)) => {
            Some(cast_num(builder, val?, cast_from, cast_to))
        }
        _ => val,
    };

    if let Some(memory) = memory {
        memory.write(val, cast_to, module, builder);
    }

    val
}

#[allow(clippy::too_many_arguments)]
fn cast_struct_to_struct(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    ptr_ty: types::Type,
    val: Option<Value>,
    cast_from: Intern<Ty>,
    cast_to: Intern<Ty>,
    memory: Option<MemoryLoc>,
) -> Option<Value> {
    assert!(cast_from.is_struct());
    assert!(cast_to.is_struct());

    let from_members = cast_from.as_struct().unwrap();
    let to_members = cast_to.as_struct().unwrap();

    assert_eq!(from_members.len(), to_members.len());

    if from_members
        .iter()
        .zip(to_members.iter())
        .all(|((from_name, from_ty), (to_name, to_ty))| {
            from_name == to_name && from_ty.is_functionally_equivalent_to(to_ty, true)
        })
    {
        val
    } else {
        let val = val?;

        // this is specifically for anonymous struct casting, although this code
        // might also be used to regular struct casting
        let result_mem = memory.unwrap_or_alloca(builder, cast_to);

        let from_layout = cast_from.struct_layout().unwrap();
        let to_layout = cast_to.struct_layout().unwrap();

        let to_members: FxHashMap<_, _> = to_members
            .iter()
            .enumerate()
            .map(|(idx, (name, ty))| (*name, (idx, *ty)))
            .collect();

        for (from_idx, (name, from_ty)) in from_members.iter().enumerate() {
            let (to_idx, to_ty) = to_members[name];

            let from_offset = from_layout.offsets()[from_idx];
            let to_offset = to_layout.offsets()[to_idx];

            let dest = result_mem.with_offset(to_offset);

            let src = if from_ty.is_aggregate() {
                Some(builder.ins().iadd_imm(val, from_offset as i64))
            } else {
                from_ty.get_final_ty().into_real_type().map(|from_ty| {
                    builder
                        .ins()
                        .load(from_ty, MemFlags::trusted(), val, from_offset as i32)
                })
            };

            cast_into_memory(
                meta_tys,
                module,
                builder,
                ptr_ty,
                src,
                *from_ty,
                to_ty,
                Some(dest),
            );
        }

        Some(result_mem.into_value(builder, ptr_ty))
    }
}

#[allow(clippy::too_many_arguments)]
fn cast_array_to_array(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    ptr_ty: types::Type,
    val: Option<Value>,
    cast_from: Intern<Ty>,
    cast_to: Intern<Ty>,
    memory: Option<MemoryLoc>,
) -> Option<Value> {
    assert!(cast_from.is_array());
    assert!(cast_to.is_array());

    let (from_len, from_sub_ty) = cast_from.as_array().unwrap();
    let (to_len, to_sub_ty) = cast_to.as_array().unwrap();

    assert_eq!(from_len, to_len);

    let from_sub_stride = from_sub_ty.stride();
    let to_sub_stride = to_sub_ty.stride();

    if from_sub_ty.is_functionally_equivalent_to(&to_sub_ty, false) {
        val
    } else {
        let val = val?;

        let result_mem = memory.unwrap_or_alloca(builder, cast_to);

        for idx in 0..to_len as u32 {
            let from_offset = from_sub_stride * idx;
            let to_offset = to_sub_stride * idx;

            let src = if from_sub_ty.is_aggregate() {
                Some(builder.ins().iadd_imm(val, from_offset as i64))
            } else {
                from_sub_ty
                    .get_final_ty()
                    .into_real_type()
                    .map(|from_sub_ty| {
                        builder.ins().load(
                            from_sub_ty,
                            MemFlags::trusted(),
                            val,
                            from_offset as i32,
                        )
                    })
            };

            let dest = result_mem.with_offset(to_offset);

            cast_into_memory(
                meta_tys,
                module,
                builder,
                ptr_ty,
                src,
                from_sub_ty,
                to_sub_ty,
                Some(dest),
            );
        }

        Some(result_mem.into_value(builder, ptr_ty))
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

    let res = match (cast_from.float, cast_to.float) {
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
    };

    res
}

pub mod comptime;
mod functions;
pub mod program;

use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{
    types, FunctionBuilder, FunctionBuilderContext, InstBuilder, MemFlags, StackSlotData,
    StackSlotKind, Value,
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir_ty::Ty;
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
    ComptimeToCompile, FinalSignature, Verbosity,
};

use self::comptime::ComptimeResult;
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
                        self.pointer_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                    data.extend_with_num_bytes(
                        align,
                        self.pointer_ty.bits() as u8,
                        self.module.isa().endianness(),
                    );
                }
            }

            if self.meta_tys.info_arrays.is_some() {
                match ty.as_ref() {
                    Ty::Array { size, sub_ty } => {
                        array_info_data.extend_with_num_bytes(
                            (*size) as u32,
                            self.pointer_ty.bits() as u8,
                            self.module.isa().endianness(),
                        );

                        let padding = layout::padding_needed_for(
                            array_info_data.len() as u32,
                            (32 / 8).min(8),
                        );
                        array_info_data.extend(std::iter::repeat(0).take(padding as usize));

                        array_info_data.extend_with_num_bytes(
                            sub_ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );

                        let ptr_size = self.pointer_ty.bytes();
                        let padding = layout::padding_needed_for(
                            array_info_data.len() as u32,
                            ptr_size.min(8),
                        );
                        array_info_data.extend(std::iter::repeat(0).take(padding as usize));
                    }
                    Ty::Slice { sub_ty } => {
                        slice_info_data.extend_with_num_bytes(
                            sub_ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Pointer { sub_ty, .. } => {
                        pointer_info_data.extend_with_num_bytes(
                            sub_ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                            32,
                            self.module.isa().endianness(),
                        );
                    }
                    Ty::Distinct { sub_ty: ty, .. } => {
                        distinct_info_data.extend_with_num_bytes(
                            ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
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
        ) {
            data_desc.define(bytes.into_boxed_slice());
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
            relocs: Vec<(u32, DataId)>,
        ) {
            data_desc.define(bytes.into_boxed_slice());

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

            let local = module.declare_data_in_data(ptr, data_desc);

            data_desc.write_data_addr(module.target_config().pointer_bytes() as u32, local, 0);

            module
                .define_data(info_array, data_desc)
                .expect("error defining data");

            data_desc.clear();
        }

        if let Some(mem_arrays) = &self.meta_tys.layout_arrays {
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.array_layout_array,
                array_mem_data,
            );
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.distinct_layout_array,
                distinct_mem_data,
            );
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.struct_layout_array,
                struct_mem_data,
            );

            define_slice(
                self.module,
                &mut self.data_description,
                mem_arrays.array_layout_slice,
                array_count,
                mem_arrays.array_layout_array,
            );
            define_slice(
                self.module,
                &mut self.data_description,
                mem_arrays.distinct_layout_slice,
                distinct_count,
                mem_arrays.distinct_layout_array,
            );
            define_slice(
                self.module,
                &mut self.data_description,
                mem_arrays.struct_layout_slice,
                struct_count,
                mem_arrays.struct_layout_array,
            );

            // pointer layout

            let mut pointer_layout_data = Vec::with_capacity(self.pointer_ty.bytes() as usize * 2);
            pointer_layout_data.extend_with_num_bytes(
                self.pointer_ty.bytes() as u32,
                self.pointer_ty.bits() as u8,
                self.module.isa().endianness(),
            );
            pointer_layout_data.extend_with_num_bytes(
                self.pointer_ty.bytes().min(8) as u32,
                self.pointer_ty.bits() as u8,
                self.module.isa().endianness(),
            );
            define(
                self.module,
                &mut self.data_description,
                mem_arrays.pointer_layout,
                pointer_layout_data,
            );
        }
        if let Some(info_arrays) = &self.meta_tys.info_arrays {
            define(
                self.module,
                &mut self.data_description,
                info_arrays.array_info_array,
                array_info_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.slice_info_array,
                slice_info_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.pointer_info_array,
                pointer_info_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.distinct_info_array,
                distinct_info_data,
            );

            define_slice(
                self.module,
                &mut self.data_description,
                info_arrays.array_info_slice,
                array_count,
                info_arrays.array_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_description,
                info_arrays.slice_info_slice,
                slice_count,
                info_arrays.slice_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_description,
                info_arrays.pointer_info_slice,
                pointer_count,
                info_arrays.pointer_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_description,
                info_arrays.distinct_info_slice,
                distinct_count,
                info_arrays.distinct_info_array,
            );
            define_slice(
                self.module,
                &mut self.data_description,
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
                        self.pointer_ty.bytes().min(8),
                    );
                    member_array_data.extend(std::iter::repeat(0).take(padding as usize));

                    // name field

                    let name_offset = member_array_data.len();

                    // zeroed-out str pointer, this will be written over later
                    member_array_data
                        .extend(std::iter::repeat(0).take(self.pointer_ty.bytes() as usize));

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
                        &mut self.data_description,
                        name_str_id,
                        name_str_bytes,
                    );

                    member_array_relocs.push((name_offset as u32, name_str_id));

                    // padding for next u32 (type)

                    let padding =
                        layout::padding_needed_for(member_array_data.len() as u32, (32 / 8).min(8));
                    member_array_data.extend(std::iter::repeat(0).take(padding as usize));

                    // ty field

                    member_array_data.extend_with_num_bytes(
                        ty.to_previous_type_id(&self.meta_tys, self.pointer_ty),
                        32,
                        self.module.isa().endianness(),
                    );

                    // padding for next usize

                    let padding = layout::padding_needed_for(
                        member_array_data.len() as u32,
                        self.pointer_ty.bytes().min(8),
                    );
                    member_array_data.extend(std::iter::repeat(0).take(padding as usize));

                    // offset field

                    member_array_data.extend_with_num_bytes(
                        member_offsets[idx],
                        self.pointer_ty.bits() as u8,
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
                &mut self.data_description,
                member_array_id,
                member_array_data,
                member_array_relocs,
            );

            // now that all the members have been defined, we can assemble the actual struct info array

            let member_array_local = self
                .module
                .declare_data_in_data(member_array_id, &mut self.data_description);

            let mut struct_array_data = Vec::new();

            for (idx, s) in struct_infos_to_compile.iter().enumerate() {
                let Ty::Struct { members, .. } = s.as_ref() else {
                    unreachable_opt_on_release!();
                };
                let members_len = members.len();

                struct_array_data.extend_with_num_bytes(
                    members_len as u32,
                    self.pointer_ty.bits() as u8,
                    self.module.isa().endianness(),
                );

                let ptr_member_offset = struct_array_data.len();

                struct_array_data.extend_with_num_bytes(
                    0,
                    self.pointer_ty.bits() as u8,
                    self.module.isa().endianness(),
                );

                let member_array_starting_offset = member_array_starting_offsets[idx];

                self.data_description.write_data_addr(
                    ptr_member_offset as u32,
                    member_array_local,
                    member_array_starting_offset as i64,
                );
            }

            define(
                self.module,
                &mut self.data_description,
                info_arrays.struct_info_array,
                struct_array_data,
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
                as_compiler_defined_func(*is_extern, &ftc, self.mod_dir, self.interner)
            {
                let (mangled, sig, func_id) = compiler_defined.to_sig_and_func_id(
                    self.module,
                    self.pointer_ty,
                    self.mod_dir,
                    self.interner,
                );

                match compiler_defined {
                    BuiltinFunction::PtrBitcast => self.compile_bitcast_fn(
                        "ptr_bitcast",
                        &mangled,
                        sig,
                        func_id,
                        self.pointer_ty,
                    ),
                    BuiltinFunction::I32Bitcast => {
                        self.compile_bitcast_fn("i32_bitcast", &mangled, sig, func_id, types::I32)
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

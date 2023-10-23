pub mod comptime;
mod functions;
pub mod program;

use cranelift::codegen::ir::Endianness;
use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{
    types, FunctionBuilder, FunctionBuilderContext, InstBuilder, IntCC, MemFlags, Value,
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir_ty::Ty;
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::compiler_defined::{as_compiler_defined, CompilerDefinedFunction};
use crate::mangle::{self, Mangle};
use crate::{convert::*, ComptimeToCompile, CraneliftSignature};

use self::comptime::ComptimeResult;
use self::functions::FunctionCompiler;

#[derive(Default)]
pub(crate) struct MetaTyData {
    pub(crate) tys_to_compile: Vec<Intern<Ty>>,

    pub(crate) array_uid_gen: UIDGenerator,
    pub(crate) pointer_uid_gen: UIDGenerator,
    pub(crate) distinct_uid_gen: UIDGenerator,
    pub(crate) function_uid_gen: UIDGenerator,
    pub(crate) struct_uid_gen: UIDGenerator,

    pub(crate) mem_arrays: Option<MetaTyMemArrays>,
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

pub(crate) struct FunctionToCompile {
    pub(crate) file_name: hir::FileName,
    pub(crate) function_name: Option<hir::Name>,
    pub(crate) lambda: Idx<hir::Lambda>,
    pub(crate) param_tys: Vec<Intern<Ty>>,
    pub(crate) return_ty: Intern<Ty>,
}

pub(crate) struct Compiler<'a> {
    pub(crate) verbose: bool,

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
    pub(crate) compiler_defined_functions: FxHashMap<CompilerDefinedFunction, FuncId>,
    pub(crate) data: FxHashMap<hir::Fqn, DataId>,
    pub(crate) meta_tys: MetaTyData,
    pub(crate) str_id_gen: UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<ComptimeToCompile, ComptimeResult>,
}

impl Compiler<'_> {
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

        if let Some(info_arrays) = &self.meta_tys.mem_arrays {
            let mut array_data = Vec::new();
            let mut distinct_data = Vec::new();
            let mut struct_data = Vec::new();

            for ty in &self.meta_tys.tys_to_compile {
                let data = match ty.as_ref() {
                    Ty::Array { .. } => &mut array_data,
                    Ty::Distinct { .. } => &mut distinct_data,
                    Ty::Struct { .. } => &mut struct_data,
                    _ => continue,
                };

                let size = ty.get_size_in_bytes(self.pointer_ty);
                let align = ty.get_align_in_bytes(self.pointer_ty);

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

            define(
                self.module,
                &mut self.data_description,
                info_arrays.array_mem,
                array_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.distinct_mem,
                distinct_data,
            );
            define(
                self.module,
                &mut self.data_description,
                info_arrays.struct_mem,
                struct_data,
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
                    CompilerDefinedFunction::PtrBitcast => {
                        self.compile_ptr_bitcast_fn(&mangled, sig, func_id)
                    }
                    CompilerDefinedFunction::SizeOf => {
                        self.compile_meta_memory_fn(&mangled, sig, func_id, true)
                    }
                    CompilerDefinedFunction::AlignOf => {
                        self.compile_meta_memory_fn(&mangled, sig, func_id, false)
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

    fn compile_ptr_bitcast_fn(
        &mut self,
        mangled_name: &str,
        sig: CraneliftSignature,
        func_id: FuncId,
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
        let arg_ptr = builder.append_block_param(entry_block, self.pointer_ty);
        builder.ins().return_(&[arg_ptr]);

        builder.seal_all_blocks();
        builder.finalize();

        if self.verbose {
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

    fn compile_meta_memory_fn(
        &mut self,
        mangled_name: &str,
        sig: CraneliftSignature,
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

        let is_simple = builder
            .ins()
            .icmp_imm(IntCC::UnsignedLessThan, discriminant, 10);

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

        let result = cast(
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

        let is_struct = builder.ins().icmp_imm(IntCC::Equal, discriminant, 14);
        builder
            .ins()
            .brif(is_struct, complex_get, &[struct_info], distinct_check, &[]);

        builder.switch_to_block(distinct_check);
        builder.seal_block(distinct_check);

        let is_distinct = builder.ins().icmp_imm(IntCC::Equal, discriminant, 12);
        builder
            .ins()
            .brif(is_distinct, complex_get, &[distinct_info], array_check, &[]);

        builder.switch_to_block(array_check);
        builder.seal_block(array_check);

        let is_array = builder.ins().icmp_imm(IntCC::Equal, discriminant, 10);
        builder
            .ins()
            .brif(is_array, complex_get, &[array_info], pointer_get, &[]);

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

        let byte_offset = cast(
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

        if self.verbose {
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
            (&param_tys, return_ty).to_cranelift_signature(self.module, self.pointer_ty);
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
            pointer_ty: self.pointer_ty,
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

        if self.verbose {
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
    compiler_defined_functions: &mut FxHashMap<CompilerDefinedFunction, FuncId>,
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

    let (comp_sig, _) = (&param_tys, return_ty).to_cranelift_signature(module, pointer_ty);

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

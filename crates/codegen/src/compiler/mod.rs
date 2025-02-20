pub mod comptime;
pub mod functions;
pub mod program;
mod ty_info;

use cranelift::codegen::ir::StackSlot;
use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{
    types, FunctionBuilder, FunctionBuilderContext, InstBuilder, MemFlags, StackSlotData,
    StackSlotKind, Value,
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir::FQComptime;
use hir_ty::{ComptimeResult, InternTyExt, ParamTy, Ty};
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::builtin::{as_compiler_defined_func, BuiltinFunction};
use crate::layout::{self, GetLayoutInfo};
use crate::mangle::{self, Mangle};
use crate::{
    convert::{self, *},
    FinalSignature, Verbosity,
};

use self::abi::Abi;
use self::functions::FunctionCompiler;

#[derive(Default)]
pub(crate) struct MetaTyData {
    // it would be more efficient to use a hashmap for this,
    // but the problem is that sometimes you'll have a type where
    // type_1 != type_2 but type_1.is_equal_to(type_2)
    //
    // as a result of this, anonymous structs will get different type ids
    //
    // todo: is this really that important?
    pub(crate) type_ids: Vec<(Intern<Ty>, u32)>,
    pub(crate) tys_to_compile: Vec<Intern<Ty>>,

    pub(crate) array_uid_gen: UIDGenerator,
    pub(crate) slice_uid_gen: UIDGenerator,
    pub(crate) pointer_uid_gen: UIDGenerator,
    pub(crate) distinct_uid_gen: UIDGenerator,
    pub(crate) variant_uid_gen: UIDGenerator,
    pub(crate) function_uid_gen: UIDGenerator,
    pub(crate) struct_uid_gen: UIDGenerator,
    pub(crate) enum_uid_gen: UIDGenerator,

    pub(crate) layout_arrays: Option<MetaTyLayoutArrays>,
    pub(crate) info_arrays: Option<MetaTyInfoArrays>,
}

pub(crate) struct MetaTyLayoutArrays {
    pub(crate) array_layout_array: DataId,
    pub(crate) distinct_layout_array: DataId,
    pub(crate) struct_layout_array: DataId,
    pub(crate) enum_layout_array: DataId,
    pub(crate) variant_layout_array: DataId,

    pub(crate) array_layout_slice: DataId,
    pub(crate) distinct_layout_slice: DataId,
    pub(crate) struct_layout_slice: DataId,
    pub(crate) enum_layout_slice: DataId,
    pub(crate) variant_layout_slice: DataId,

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
            enum_layout_array: declare("enum_layout_array"),
            enum_layout_slice: declare("enum_layout_slice"),
            variant_layout_array: declare("variant_layout_array"),
            variant_layout_slice: declare("variant_layout_slice"),
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
    pub(crate) enum_info_array: DataId,
    pub(crate) variant_info_array: DataId,

    // the global slices available in "meta.capy"
    pub(crate) array_info_slice: DataId,
    pub(crate) slice_info_slice: DataId,
    pub(crate) pointer_info_slice: DataId,
    pub(crate) distinct_info_slice: DataId,
    pub(crate) struct_info_slice: DataId,
    pub(crate) enum_info_slice: DataId,
    pub(crate) variant_info_slice: DataId,
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
            enum_info_array: declare("enum_info_array"),
            enum_info_slice: declare("enum_info_slice"),
            variant_info_array: declare("variant_info_array"),
            variant_info_slice: declare("variant_info_slice"),
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
    pub(crate) param_tys: Vec<ParamTy>,
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
    pub(crate) cmd_args_slice: Option<DataId>,
    pub(crate) str_id_gen: UIDGenerator,
    pub(crate) i128_id_gen: UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<FQComptime, ComptimeResult>,
    pub(crate) comptime_data: FxHashMap<FQComptime, ComptimeData>,

    pub(crate) default_abi: Abi,
}

/// The order of functions to call is this:
///
/// ```text
/// compiler.finalize_tys();
/// compiler.compile_queued();
/// compiler.compile_builtins();
/// ```
impl Compiler<'_> {
    /// Should be called before `Compiler::compile_queued`.
    ///
    /// `finalize_tys` will calculate the final size, stride, alignment, and `FinalTy`
    /// of every `Intern<Ty>` used in the Capy program.
    fn finalize_tys(&mut self) {
        layout::calc_layouts(self.tys.all_tys(), self.ptr_ty.bits());
        convert::calc_finals(self.tys.all_tys(), self.ptr_ty);
    }

    /// This is the function that does the actual work.
    ///
    /// It iteratively compiles every used function into cranelift IR.
    /// This only happens for functions/globals reached by the entry point.
    fn compile_queued(&mut self) {
        while let Some(ftc) = self.functions_to_compile.pop_front() {
            self.compile_ftc(ftc);
        }
    }

    /// This should be run *after* `Compiler::compile_queued`.
    ///
    /// `compile_queued` will mark certain builtin globals as "accessed".
    /// This function then only populated those builtin globals with
    /// their expected values
    fn compile_builtins(&mut self) {
        ty_info::compile_meta_builtins(self);

        if let Some(cmd_args_slice) = self.cmd_args_slice {
            self.data_desc
                .define_zeroinit(self.ptr_ty.bytes() as usize * 2);
            self.data_desc.set_align(self.ptr_ty.bytes() as u64);
            self.module
                .define_data(cmd_args_slice, &self.data_desc)
                .expect("error defining data");
            self.data_desc.clear();
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
                BuiltinFunction::ConcreteBitcast(ty) => {
                    self.compile_bitcast_fn(&format!("{ty}_bitcast"), &mangled, sig, func_id, ty)
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

        // This function literally just returns what it was given.
        // Could we make calls to `ptr.from_raw()` or `ptr.to_raw()` noop?
        // Yes, probably.
        // TODO: Only compile these builtin functions if they are used as first class functions
        let arg = builder.append_block_param(entry_block, ty);
        builder.ins().return_(&[arg]);

        builder.seal_all_blocks();
        builder.finalize();

        if matches!(self.verbosity, Verbosity::AllFunctions { .. }) {
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
        param_tys: Vec<ParamTy>,
        return_ty: Intern<Ty>,
    ) -> FuncId {
        self.compile_real_function_with_abi(
            unmangled_name,
            mangled_name,
            module_name,
            body,
            param_tys,
            return_ty,
            self.default_abi,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_real_function_with_abi(
        &mut self,
        unmangled_name: &str,
        mangled_name: &str,
        module_name: hir::FileName,
        body: Idx<hir::Expr>,
        param_tys: Vec<ParamTy>,
        return_ty: Intern<Ty>,
        abi: Abi,
    ) -> FuncId {
        let fn_abi = abi.fn_to_target((&param_tys, return_ty));
        let comp_sig = fn_abi.to_cl(self.ptr_ty, self.module.target_config().default_call_conv);
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
            cmd_args_slice: &mut self.cmd_args_slice,
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
            switch_locals: FxHashMap::default(),
            params: FxHashMap::default(),
            exits: FxHashMap::default(),
            continues: FxHashMap::default(),
            defer_stack: Vec::new(),
        };

        let is_mod = module_name.is_mod(self.mod_dir, self.interner);

        if self.verbosity.should_show(is_mod) {
            println!("{} \x1B[90m{}\x1B[0m:", unmangled_name, mangled_name);
        }

        function_compiler.finish(
            fn_abi,
            (&param_tys, return_ty),
            body,
            self.verbosity.should_show(is_mod),
        );

        if self.verbosity.include_disasm(is_mod) {
            self.ctx.want_disasm = true;
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

        let compiled = self.ctx.compiled_code().unwrap();

        if self.verbosity.include_disasm(is_mod) {
            print!("asm = \n{}", compiled.vcode.as_ref().unwrap());
            println!(
                "({} instructions, {} bytes of machine code)",
                compiled
                    .vcode
                    .as_ref()
                    .unwrap()
                    .lines()
                    .filter(|l| !l.ends_with(':'))
                    .count(),
                compiled.code_buffer().len(),
            );
            println!("stack frame size = {} bytes\n", compiled.frame_size);
        }

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
            .to_cl(pointer_ty, module.target_config().default_call_conv);

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
        hir::Expr::Member {
            previous,
            name: field,
        } => {
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
            .to_cl(pointer_ty, module.target_config().default_call_conv);

        let func_id = module
            .declare_function(interner.lookup(fqn.name.0), Linkage::Import, &comp_sig)
            .expect("There are multiple extern functions with the same name");

        functions.insert(fqn, func_id);

        return func_id;
    }

    functions_to_compile.push_back(ftc);

    let comp_sig = Into::<Abi>::into(module.target_config())
        .fn_to_target((&param_tys, return_ty))
        .to_cl(pointer_ty, module.target_config().default_call_conv);

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
                Location::Addr(mut addr) => {
                    if self.offset != 0 {
                        addr = builder.ins().iadd_imm(addr, self.offset as i64);
                    }
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
                    align_shift: ty.align_shift(),
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

    let cast_from_original = cast_from;

    let mut cast_from = cast_from.absolute_intern_ty(false);
    let cast_to = cast_to.absolute_intern_ty(true);

    // first we check for variant -> enum
    if let (
        Ty::Variant {
            enum_uid: from_enum_uid,
            uid,
            sub_ty,
            discriminant,
            ..
        },
        Ty::Enum {
            uid: to_enum_uid,
            variants,
            ..
        },
    ) = (cast_from.as_ref(), cast_to.as_ref())
    {
        assert_eq!(from_enum_uid, to_enum_uid);

        let enum_layout = cast_to.enum_layout().unwrap();

        let found_sub_ty = variants
            .iter()
            .find_map(|v| {
                let Ty::Variant {
                    uid: variant_uid,
                    sub_ty,
                    ..
                } = v.as_ref()
                else {
                    unreachable!("all variants should be `Ty::Variant`")
                };
                if variant_uid == uid {
                    Some(sub_ty)
                } else {
                    None
                }
            })
            .expect("variants can only be casted to their own enums");
        assert_eq!(sub_ty, found_sub_ty);

        let memory = memory.unwrap_or_alloca(builder, cast_to);

        memory.write(val, *sub_ty, module, builder);

        let discrim = builder.ins().iconst(ptr_ty, *discriminant as i64);
        memory.store(builder, discrim, enum_layout.discriminant_offset() as i32);

        return Some(memory.into_value(builder, ptr_ty));
    }

    // if it wasn't variant -> enum, we unwrap the variant fully and check for other casts
    cast_from = cast_from.absolute_intern_ty(true);

    match (cast_from.as_ref(), cast_to.as_ref()) {
        (Ty::Array { size, .. }, Ty::Slice { .. }) => {
            let memory = memory.unwrap_or_alloca(builder, cast_to);

            let len = builder.ins().iconst(ptr_ty, *size as i64);
            memory.store(builder, len, 0_i32);
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
        (_, Ty::Any) => {
            let any_mem = memory.unwrap_or_alloca(builder, cast_to);

            let typeid_size = 32 / 8;
            let typeid_offset = 0;

            let rawptr_size = ptr_ty.bytes();
            let rawptr_align = rawptr_size.min(8);
            let rawptr_offset = typeid_size + layout::padding_needed_for(typeid_size, rawptr_align);

            let typeid = cast_from_original.to_type_id(meta_tys, ptr_ty) as i64;
            let typeid = builder.ins().iconst(types::I32, typeid);
            any_mem.store(builder, typeid, typeid_offset);

            if let Some(val) = val {
                let ptr = if cast_from.is_aggregate() {
                    val
                } else {
                    let tmp_stack_slot = builder.create_sized_stack_slot(StackSlotData {
                        kind: StackSlotKind::ExplicitSlot,
                        size: cast_from.size(),
                        align_shift: cast_from.align_shift(),
                    });

                    builder.ins().stack_store(val, tmp_stack_slot, 0);

                    builder.ins().stack_addr(ptr_ty, tmp_stack_slot, 0)
                };

                any_mem.store(builder, ptr, rawptr_offset as i32);
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
        .all(|(from, to)| {
            from.name == to.name && from.ty.is_functionally_equivalent_to(&to.ty, true)
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
            .map(|(idx, member_ty)| (member_ty.name, (idx, member_ty.ty)))
            .collect();

        for (
            from_idx,
            hir_ty::MemberTy {
                name: from_name,
                ty: from_ty,
            },
        ) in from_members.iter().enumerate()
        {
            let (to_idx, to_ty) = to_members[from_name];

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

pub mod comptime;
pub mod functions;
pub mod program;
mod ty_info;

use cranelift::codegen::ir::{BlockArg, StackSlot};
use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{
    types, FunctionBuilder, FunctionBuilderContext, InstBuilder, IntCC, MemFlags, StackSlotData,
    StackSlotKind, Value,
};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir::FQComptime;
use hir_ty::{ComptimeResult, InternTyExt, ParamTy, Ty};
use interner::Interner;
use internment::Intern;
use itertools::Itertools;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::str::FromStr;
use uid_gen::UIDGenerator;

use crate::builtin::BuiltinFunction;
use crate::debug::NiceFuncWriter;
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
    pub(crate) variant_uid_gen: UIDGenerator,
    pub(crate) function_uid_gen: UIDGenerator,
    pub(crate) struct_uid_gen: UIDGenerator,
    pub(crate) enum_uid_gen: UIDGenerator,
    pub(crate) distinct_uid_gen: UIDGenerator,
    pub(crate) optional_uid_gen: UIDGenerator,
    pub(crate) error_union_uid_gen: UIDGenerator,

    pub(crate) layout_arrays: Option<MetaTyLayoutArrays>,
    pub(crate) info_arrays: Option<MetaTyInfoArrays>,
}

pub(crate) struct MetaTyLayoutArrays {
    pub(crate) array_layout_array: DataId,
    pub(crate) distinct_layout_array: DataId,
    pub(crate) struct_layout_array: DataId,
    pub(crate) enum_layout_array: DataId,
    pub(crate) variant_layout_array: DataId,
    pub(crate) optional_layout_array: DataId,
    pub(crate) error_union_layout_array: DataId,

    pub(crate) array_layout_slice: DataId,
    pub(crate) distinct_layout_slice: DataId,
    pub(crate) struct_layout_slice: DataId,
    pub(crate) enum_layout_slice: DataId,
    pub(crate) variant_layout_slice: DataId,
    pub(crate) optional_layout_slice: DataId,
    pub(crate) error_union_layout_slice: DataId,

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
            optional_layout_array: declare("optional_layout_array"),
            optional_layout_slice: declare("optional_layout_slice"),
            error_union_layout_array: declare("error_union_layout_array"),
            error_union_layout_slice: declare("error_union_layout_slice"),
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
    pub(crate) optional_info_array: DataId,
    pub(crate) error_union_info_array: DataId,

    // the global slices available in "meta.capy"
    pub(crate) array_info_slice: DataId,
    pub(crate) slice_info_slice: DataId,
    pub(crate) pointer_info_slice: DataId,
    pub(crate) distinct_info_slice: DataId,
    pub(crate) struct_info_slice: DataId,
    pub(crate) enum_info_slice: DataId,
    pub(crate) variant_info_slice: DataId,
    pub(crate) optional_info_slice: DataId,
    pub(crate) error_union_info_slice: DataId,
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
            optional_info_array: declare("optional_info_array"),
            optional_info_slice: declare("optional_info_slice"),
            error_union_info_array: declare("error_union_info_array"),
            error_union_info_slice: declare("error_union_info_slice"),
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
    pub(crate) user_extern_functions: FxHashMap<hir::Name, FuncId>,
    pub(crate) internal_extern_functions: FxHashMap<&'static str, FuncId>,
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
            &mut self.user_extern_functions,
            &mut self.internal_extern_functions,
            &mut self.compiler_defined_functions,
            &mut self.functions_to_compile,
            self.tys,
            self.world_bodies,
            self.interner,
            fqn,
        )
    }

    fn compile_ftc(&mut self, ftc: FunctionToCompile) {
        let hir::Lambda { body, .. } = &self.world_bodies[ftc.file_name][ftc.lambda];

        if let hir::LambdaBody::Builtin { name, .. } = body {
            let builtin_kind = hir_ty::BuiltinKind::from_str(self.interner.lookup(*name)).unwrap();
            let builtin_func: BuiltinFunction = builtin_kind.into();

            let (mangled, sig, func_id) = builtin_func.to_sig_and_func_id(
                self.module,
                self.ptr_ty,
                self.mod_dir,
                self.interner,
            );

            match builtin_func {
                BuiltinFunction::PtrBitcast => {
                    self.compile_bitcast_fn("ptr_bitcast", &mangled, sig, func_id, self.ptr_ty)
                }
                BuiltinFunction::ConcreteBitcast(ty) => {
                    self.compile_bitcast_fn(&format!("{ty}_bitcast"), &mangled, sig, func_id, ty)
                }
            }
            return;
        }

        if *body == hir::LambdaBody::Extern {
            unreachable!("regular extern functions should not be pushed to `functions_to_compile`");
        }

        let hir::LambdaBody::Block(body) = body else {
            unreachable!("hir::LambdaBody::Empty would've reported an error");
        };

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
            user_extern_functions: &mut self.user_extern_functions,
            internal_extern_functions: &mut self.internal_extern_functions,
            compiler_defined_functions: &mut self.compiler_defined_functions,
            globals: &mut self.data,
            str_id_gen: &mut self.str_id_gen,
            i128_id_gen: &mut self.i128_id_gen,
            comptime_results: self.comptime_results,
            comptime_data: &mut self.comptime_data,
            locals: FxHashMap::default(),
            switch_locals: FxHashMap::default(),
            params: FxHashMap::default(),
            exits: FxHashMap::default(),
            continues: FxHashMap::default(),
            defer_stack: Vec::new(),
            func_writer: Default::default(),
        };

        let is_mod = module_name.is_mod(self.mod_dir, self.interner);

        if self.verbosity.should_show(is_mod) {
            println!("({})", unmangled_name);
        }

        // `finish` will print the cranelift ir itself
        function_compiler.finish(
            fn_abi,
            (&param_tys, return_ty),
            body,
            self.verbosity.should_show(is_mod),
            mangled_name,
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

fn get_func_id(
    module: &mut dyn Module,
    pointer_ty: types::Type,
    mod_dir: &std::path::Path,
    functions: &mut FxHashMap<hir::Fqn, FuncId>,
    user_extern_functions: &mut FxHashMap<hir::Name, FuncId>,
    internal_extern_functions: &mut FxHashMap<&'static str, FuncId>,
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
        if let Some(func_id) = user_extern_functions.get(&fqn.name) {
            return *func_id;
        }
        if let Some(func_id) = internal_extern_functions.get(interner.lookup(fqn.name.0)) {
            user_extern_functions.insert(fqn.name, *func_id);
            return *func_id;
        }

        let comp_sig = Into::<Abi>::into(module.target_config())
            .fn_to_target((&param_tys, return_ty))
            .to_cl(pointer_ty, module.target_config().default_call_conv);

        let func_id = module
            .declare_function(interner.lookup(fqn.name.0), Linkage::Import, &comp_sig)
            .expect("There are multiple extern functions with the same name");

        user_extern_functions.insert(fqn.name, func_id);

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
                user_extern_functions,
                internal_extern_functions,
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
                    user_extern_functions,
                    internal_extern_functions,
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

    let ftc = FunctionToCompile {
        file_name: fqn.file,
        function_name: Some(fqn.name),
        lambda,
        param_tys: param_tys.clone(),
        return_ty,
    };

    let lambda_body = &world_bodies[fqn.file][lambda];

    if let hir::LambdaBody::Builtin { name, .. } = lambda_body.body {
        let builtin_kind = hir_ty::BuiltinKind::from_str(interner.lookup(name)).unwrap();
        let builtin_func: BuiltinFunction = builtin_kind.into();

        if let Some(func_id) = compiler_defined_functions.get(&builtin_func) {
            functions.insert(fqn, *func_id);

            return *func_id;
        }

        let (_, _, func_id) =
            builtin_func.to_sig_and_func_id(module, pointer_ty, mod_dir, interner);

        functions_to_compile.push_back(ftc);

        compiler_defined_functions.insert(builtin_func, func_id);
        functions.insert(fqn, func_id);

        return func_id;
    }

    if lambda_body.body == hir::LambdaBody::Extern {
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

    /// As opposed to `write_all`, this writes a single `Value` to an `offset`
    fn write_val(&self, builder: &mut FunctionBuilder, x: Value, offset: i32) {
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

    /// Does a simple write or a memmove if necessary
    /// Unlike `write_val`, this writes an *entire* object into the memory
    ///
    /// By using this function, you promise that the bytes of val can fit inside
    /// the given MemoryLoc.
    ///
    /// You also promise that the alignment of val matches the alignment of the
    /// the given MemoryLoc.
    fn write_all(
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

    /// writes the byte `val` into every byte of `ty`
    fn memset(
        self,
        module: &mut dyn Module,
        builder: &mut FunctionBuilder,
        val: u8,
        ty: Intern<Ty>,
    ) {
        match self.addr {
            Location::Addr(mut addr) => {
                if self.offset != 0 {
                    addr = builder.ins().iadd_imm(addr, self.offset as i64);
                }
                builder.emit_small_memset(
                    module.target_config(),
                    addr,
                    val,
                    ty.size() as u64,
                    ty.align() as u8,
                    MemFlags::trusted(),
                );
            }
            Location::Stack(slot) => {
                // be very explicit to cranelift what we are doing here
                // since there is no `emit_stack_memcpy`, do it ourselves
                let mut off = 0;
                macro_rules! mem_cpy_loop {
                    ($width:expr) => {
                        while (off + $width) <= (ty.stride() as i32 / $width) * $width {
                            let val = builder.ins().iconst(
                                cranelift::codegen::ir::Type::int_with_byte_size(8).unwrap(),
                                val as i64,
                            );
                            builder
                                .ins()
                                .stack_store(val, slot, off + self.offset as i32);
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

fn cast_into_memory(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    func_writer: &mut NiceFuncWriter,
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

                memory.write_all(val, cast_to, module, builder);

                return Some(memory.into_value(builder, ptr_ty));
            }
            None => return val,
        }
    }

    let cast_from_original = cast_from;

    let mut cast_from = cast_from.absolute_intern_ty(false);
    let cast_to = cast_to.absolute_intern_ty(true);

    if *cast_from == Ty::AlwaysJumps {
        assert_eq!(val, None);
        return val;
    }

    // first we check for variant -> enum
    // we do this before cast_from gets absoluted
    if let (
        Ty::EnumVariant {
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
                let Ty::EnumVariant {
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

        memory.write_all(val, *sub_ty, module, builder);

        let discrim = builder.ins().iconst(ptr_ty, *discriminant as i64);
        memory.write_val(builder, discrim, enum_layout.discriminant_offset() as i32);

        return Some(memory.into_value(builder, ptr_ty));
    }

    // if it wasn't variant -> enum, we unwrap the variant fully and check for other casts
    cast_from = cast_from.absolute_intern_ty(true);

    match (cast_from.as_ref(), cast_to.as_ref()) {
        (
            Ty::AnonStruct { .. } | Ty::ConcreteStruct { .. },
            Ty::AnonStruct { .. } | Ty::ConcreteStruct { .. },
        ) => {
            return cast_struct_to_struct(
                meta_tys,
                module,
                builder,
                func_writer,
                ptr_ty,
                val,
                cast_from,
                cast_to,
                memory,
            );
        }
        (
            Ty::AnonArray { .. } | Ty::ConcreteArray { .. },
            Ty::AnonArray { .. } | Ty::ConcreteArray { .. },
        ) => {
            return cast_array_to_array(
                meta_tys,
                module,
                builder,
                func_writer,
                ptr_ty,
                val,
                cast_from,
                cast_to,
                memory,
            );
        }
        (Ty::AnonArray { size, .. } | Ty::ConcreteArray { size, .. }, Ty::Slice { .. }) => {
            let memory = memory.unwrap_or_alloca(builder, cast_to);

            let len = builder.ins().iconst(ptr_ty, *size as i64);
            memory.write_val(builder, len, 0_i32);
            // todo: will this cause errors? what happens if you do slice[5] or ^slice[5]?
            if let Some(val) = val {
                memory.write_val(builder, val, ptr_ty.bytes() as i32);
            }

            return Some(memory.into_value(builder, ptr_ty));
        }
        (Ty::Slice { .. }, Ty::AnonArray { .. } | Ty::ConcreteArray { .. }) => {
            // todo: do a runtime check that the lengths match

            return Some(builder.ins().load(
                ptr_ty,
                MemFlags::trusted(),
                val?,
                // the second field (after usize len) is the addr of the array
                ptr_ty.bytes() as i32,
            ));
        }
        (Ty::Nil, Ty::Optional { .. }) => {
            return Some(create_nil_value(builder, ptr_ty, cast_to, memory));
        }
        (Ty::Optional { sub_ty: from_sub }, Ty::Optional { sub_ty: to_sub }) => {
            assert!(
                from_sub.can_cast_to(to_sub),
                "{from_sub:?} can not cast to {to_sub:?}"
            );

            let opt = val.expect("the found type is an option so val should be Some");

            return optional_map(
                builder,
                func_writer,
                cast_from,
                opt,
                true,
                |builder, func_writer, payload| {
                    // this will reuse the (_, Ty::Optional) cast defined below because I don't want
                    // to implement it again
                    let new_opt = cast_into_memory(
                        meta_tys,
                        module,
                        builder,
                        func_writer,
                        ptr_ty,
                        payload,
                        *from_sub,
                        cast_to,
                        memory,
                    )
                    .expect("since we're casting to an optional, we should get a value");

                    Some(new_opt)
                },
                |builder, _func_writer| Some(create_nil_value(builder, ptr_ty, cast_to, memory)),
                cast_to.get_final_ty().into_real_type(),
            );
        }
        (_, Ty::Optional { sub_ty }) => {
            assert!(
                cast_from.can_cast_to(sub_ty),
                "{cast_from:?} can not cast to {sub_ty:?}"
            );

            if cast_to.is_tagged_union() {
                assert!(cast_to.is_aggregate());

                return Some(cast_payload_into_tagged_union(
                    meta_tys,
                    module,
                    builder,
                    func_writer,
                    ptr_ty,
                    val,
                    cast_from,
                    *sub_ty,
                    cast_to,
                    1,
                    memory,
                ));
            } else {
                assert!(!cast_to.is_aggregate());
                assert!(sub_ty.is_non_zero());

                return cast_into_memory(
                    meta_tys,
                    module,
                    builder,
                    func_writer,
                    ptr_ty,
                    val,
                    cast_from,
                    *sub_ty,
                    memory,
                );
            }
        }
        (
            Ty::ErrorUnion {
                error_ty: from_error_ty,
                payload_ty: from_payload_ty,
            },
            Ty::ErrorUnion {
                error_ty: to_error_ty,
                payload_ty: to_payload_ty,
            },
        ) => {
            // Because I'm not sure how safe it is to cast undefined nil memory, we only do actual
            // casting if the first optional isn't nil

            assert!(
                from_error_ty.can_cast_to(to_error_ty)
                    && from_payload_ty.can_cast_to(to_payload_ty),
                "{from_error_ty:?} and {from_payload_ty:?} can not cast to {to_error_ty:?} and {to_payload_ty:?}"
            );

            let val = val.expect("the found type is an option so val should be Some");

            assert!(cast_to.is_error_union());
            return error_union_map(
                meta_tys,
                module,
                builder,
                func_writer,
                cast_from,
                val,
                true,
                |meta_tys, module, builder, func_writer, payload| {
                    Some(cast_payload_into_tagged_union(
                        meta_tys,
                        module,
                        builder,
                        func_writer,
                        ptr_ty,
                        payload,
                        *from_payload_ty,
                        *to_payload_ty,
                        cast_to,
                        1,
                        memory,
                    ))
                },
                |meta_tys, module, builder, func_writer, error| {
                    Some(cast_payload_into_tagged_union(
                        meta_tys,
                        module,
                        builder,
                        func_writer,
                        ptr_ty,
                        error,
                        *from_error_ty,
                        *to_error_ty,
                        cast_to,
                        0,
                        memory,
                    ))
                },
                cast_to.get_final_ty().into_real_type(),
            );
        }
        // ok to error union
        (_, Ty::ErrorUnion { payload_ty, .. }) if cast_from.can_fit_into(payload_ty) => {
            return Some(cast_payload_into_tagged_union(
                meta_tys,
                module,
                builder,
                func_writer,
                ptr_ty,
                val,
                cast_from,
                *payload_ty,
                cast_to,
                1,
                memory,
            ));
        }
        // error to error union
        (_, Ty::ErrorUnion { error_ty, .. }) if cast_from.can_fit_into(error_ty) => {
            return Some(cast_payload_into_tagged_union(
                meta_tys,
                module,
                builder,
                func_writer,
                ptr_ty,
                val,
                cast_from,
                *error_ty,
                cast_to,
                0,
                memory,
            ));
        }
        (_, Ty::ErrorUnion { .. }) => unreachable!(
            "the previous two arms should've caught this: {cast_from:?} -> {cast_to:?}"
        ),
        // todo: try to pass a singleton into a function that takes types
        (_, Ty::Type) => {
            assert!(cast_from.is_zero_sized());

            let id = cast_from_original.to_type_id(meta_tys, ptr_ty);
            let id = builder.ins().iconst(types::I32, id as i64);

            if let Some(memory) = memory {
                assert_eq!(cast_from.align(), cast_to.align());

                memory.write_val(builder, id, 0);
            }

            return Some(id);
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
            any_mem.write_val(builder, typeid, typeid_offset);

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

                any_mem.write_val(builder, ptr, rawptr_offset as i32);
            }

            return Some(any_mem.into_value(builder, ptr_ty));
        }
        // todo: do these string casts also need to be caught the other way?
        (Ty::Pointer { .. } | Ty::RawPtr { .. }, Ty::Pointer { .. } | Ty::RawPtr { .. })
        | (Ty::Slice { .. } | Ty::RawSlice, Ty::Slice { .. } | Ty::RawSlice)
        | (
            Ty::String,
            Ty::AnonArray { .. }
            | Ty::ConcreteArray { .. }
            | Ty::Pointer { .. }
            | Ty::RawPtr { .. },
        ) => {
            if let Some(memory) = memory
                && let Some(val) = val
            {
                // memory.write_all(val, cast_to, module, builder);
                memory.write_val(builder, val, 0);
            }

            return val;
        }
        _ => {}
    }

    // it's a simple cast

    assert!(
        !cast_from.is_aggregate() && !cast_to.is_aggregate(),
        "{cast_from:?} -> {cast_to:?} is an aggregate cast but it hasn't been handled yet"
    );

    let val = match (cast_from.get_final_ty(), cast_to.get_final_ty()) {
        (FinalTy::Number(cast_from), FinalTy::Number(cast_to)) => {
            Some(cast_num(builder, val?, cast_from, cast_to))
        }
        _ => panic!("unhandled cast {cast_from:?} -> {cast_to:?}"),
    };

    if let Some(memory) = memory {
        memory.write_all(val, cast_to, module, builder);
    }

    val
}

fn cast_struct_to_struct(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    func_writer: &mut NiceFuncWriter,
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
        .zip_eq(to_members.iter())
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
                func_writer,
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

fn cast_array_to_array(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    func_writer: &mut NiceFuncWriter,
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
                func_writer,
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

fn cast_payload_into_tagged_union(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    func_writer: &mut NiceFuncWriter,
    ptr_ty: types::Type,
    val: Option<Value>,
    from_payload_ty: Intern<Ty>,
    to_payload_ty: Intern<Ty>,
    union_ty: Intern<Ty>,
    discrim: i64,
    memory: Option<MemoryLoc>,
) -> Value {
    // todo: should absolute_ty be called?
    assert!(union_ty.is_tagged_union());
    assert!(union_ty.is_aggregate());
    assert!(
        from_payload_ty.can_cast_to(&to_payload_ty),
        "{from_payload_ty:?} can not cast to {to_payload_ty:?}"
    );

    let memory = memory.unwrap_or_alloca(builder, union_ty);

    cast_into_memory(
        meta_tys,
        module,
        builder,
        func_writer,
        ptr_ty,
        val,
        from_payload_ty,
        to_payload_ty,
        Some(memory),
    );

    let enum_layout = union_ty
        .enum_layout()
        .expect("we already checked that the type was a tagged union");
    let one = builder.ins().iconst(types::I8, discrim);
    memory.write_val(builder, one, enum_layout.discriminant_offset() as i32);

    memory.into_value(builder, ptr_ty)
}

// This works for tagged unions and nullable pointers.
//
// Note: this doesn't check the tag of the tagged union
fn unwrap_sum_ty(
    builder: &mut FunctionBuilder,
    union_ptr: Value,
    union_ty: Intern<Ty>,
    payload_ty: Intern<Ty>,
) -> Option<Value> {
    assert!(union_ty.is_sum_ty(), "{union_ty:?} is not a sum type");
    assert!(
        union_ty.has_sum_variant(&payload_ty),
        "{payload_ty:?} is not a variant of {union_ty:?}"
    );

    if !union_ty.is_tagged_union() {
        assert!(union_ty.is_optional());

        if *payload_ty == Ty::Nil {
            return None;
        } else {
            assert!(payload_ty.is_non_zero(), "{payload_ty:?} can be zero");
            return Some(union_ptr);
        }
    }

    if !payload_ty.is_aggregate()
        && let Some(final_ty) = payload_ty.get_final_ty().into_real_type()
    {
        assert!(!payload_ty.is_non_zero());

        Some(
            builder
                .ins()
                .load(final_ty, MemFlags::trusted(), union_ptr, 0),
        )
    } else if payload_ty.is_zero_sized() {
        None
    } else {
        assert!(payload_ty.is_aggregate());
        Some(union_ptr)
    }
}

fn create_nil_value(
    builder: &mut FunctionBuilder,
    ptr_ty: types::Type,
    option_ty: Intern<Ty>,
    memory: Option<MemoryLoc>,
) -> Value {
    let Ty::Optional { sub_ty } = option_ty.absolute_ty() else {
        unreachable!("the type of nil should be an optional");
    };

    if sub_ty.is_non_zero() {
        assert!(!sub_ty.is_aggregate());

        let real_ty = sub_ty
            .get_final_ty()
            .into_real_type()
            .expect("non_zero is never void");

        let nil = builder.ins().iconst(real_ty, 0);

        if let Some(memory) = memory {
            memory.write_val(builder, nil, 0);
        }

        nil
    } else {
        assert!(option_ty.is_aggregate());

        let opt_layout = option_ty
            .enum_layout()
            .expect("all non-pointer options should have an enum layout");

        let memory = memory.unwrap_or_alloca(builder, option_ty);

        let zero = builder.ins().iconst(types::I8, 0);
        memory.write_val(builder, zero, opt_layout.discriminant_offset() as i32);

        memory.into_value(builder, ptr_ty)
    }
}

fn optional_map(
    builder: &mut FunctionBuilder,
    func_writer: &mut NiceFuncWriter,
    option_ty: Intern<Ty>,
    val: Value,
    unwrap_option: bool,
    map_payload: impl FnOnce(&mut FunctionBuilder, &mut NiceFuncWriter, Option<Value>) -> Option<Value>,
    map_nil: impl FnOnce(&mut FunctionBuilder, &mut NiceFuncWriter) -> Option<Value>,
    finally_ret: Option<types::Type>,
) -> Option<Value> {
    let Ty::Optional { sub_ty: payload_ty } = option_ty.absolute_ty() else {
        panic!("{option_ty:?} is not an optional");
    };

    let err_block = builder.create_block();
    func_writer[err_block] = "optional_map_error".into();
    let some_block = builder.create_block();
    func_writer[some_block] = "optional_map_okay".into();
    let finally_block = builder.create_block();
    func_writer[finally_block] = "optional_map_exit".into();

    if let Some(finally_ret) = finally_ret {
        builder.append_block_param(finally_block, finally_ret);
    }

    let is_some = optional_is_some(builder, option_ty, val);

    builder.ins().brif(is_some, some_block, &[], err_block, &[]);
    builder.seal_block(some_block);
    builder.seal_block(err_block);

    builder.switch_to_block(some_block);

    let some_val = if unwrap_option {
        // todo: I think this needs to take the payload type and not the optional type
        unwrap_sum_ty(builder, val, option_ty, *payload_ty)
    } else {
        None
    };

    match map_payload(builder, func_writer, some_val) {
        Some(val) => {
            builder.ins().jump(finally_block, &[BlockArg::Value(val)]);
        }
        None => {
            builder.ins().jump(finally_block, &[]);
        }
    }

    builder.switch_to_block(err_block);

    match map_nil(builder, func_writer) {
        Some(val) => {
            builder.ins().jump(finally_block, &[BlockArg::Value(val)]);
        }
        None => {
            builder.ins().jump(finally_block, &[]);
        }
    }

    builder.switch_to_block(finally_block);
    builder.seal_block(finally_block);

    if finally_ret.is_some() {
        Some(builder.block_params(finally_block)[0])
    } else {
        None
    }
}

fn optional_is_some(builder: &mut FunctionBuilder, option_ty: Intern<Ty>, val: Value) -> Value {
    let Ty::Optional { sub_ty } = *option_ty else {
        unreachable!(
            "the function is literally named `optional_is_some`. what the hell are you doing trying to pass something a non-optional to it????"
        )
    };

    if sub_ty.is_non_zero() {
        // if aggregate non-zero types are added, we have to do a memcmp
        assert!(!option_ty.is_aggregate());
        assert!(sub_ty.is_pointer());

        builder.ins().icmp_imm(IntCC::NotEqual, val, 0)
    } else {
        tagged_union_has_discriminant(builder, option_ty, val, 1)
    }
}

fn error_union_map(
    meta_tys: &mut MetaTyData,
    module: &mut dyn Module,
    builder: &mut FunctionBuilder,
    func_writer: &mut NiceFuncWriter,
    error_union_ty: Intern<Ty>,
    val: Value,
    unwrap_union: bool,
    map_payload: impl FnOnce(
        &mut MetaTyData,
        &mut dyn Module,
        &mut FunctionBuilder,
        &mut NiceFuncWriter,
        Option<Value>,
    ) -> Option<Value>,
    map_error: impl FnOnce(
        &mut MetaTyData,
        &mut dyn Module,
        &mut FunctionBuilder,
        &mut NiceFuncWriter,
        Option<Value>,
    ) -> Option<Value>,
    finally_ret: Option<types::Type>,
) -> Option<Value> {
    let Ty::ErrorUnion {
        error_ty,
        payload_ty,
    } = *error_union_ty
    else {
        unreachable!(
            "the function is literally named `error_union_is_payload`. what the hell are you doing trying to pass something a non-optional to it????"
        )
    };

    let err_block = builder.create_block();
    func_writer[err_block] = "error_union_map_error".into();
    let ok_block = builder.create_block();
    func_writer[ok_block] = "error_union_map_okay".into();
    let finally_block = builder.create_block();
    func_writer[finally_block] = "error_union_map_exit".into();

    if let Some(finally_ret) = finally_ret {
        builder.append_block_param(finally_block, finally_ret);
    }

    let is_ok = tagged_union_has_discriminant(builder, error_union_ty, val, 1);

    builder.ins().brif(is_ok, ok_block, &[], err_block, &[]);
    builder.seal_block(ok_block);
    builder.seal_block(err_block);

    builder.switch_to_block(ok_block);

    let ok_val = if unwrap_union {
        unwrap_sum_ty(builder, val, error_union_ty, payload_ty)
    } else {
        None
    };

    match map_payload(meta_tys, module, builder, func_writer, ok_val) {
        Some(val) => {
            builder.ins().jump(finally_block, &[BlockArg::Value(val)]);
        }
        None => {
            builder.ins().jump(finally_block, &[]);
        }
    }

    builder.switch_to_block(err_block);

    let err_val = if unwrap_union {
        unwrap_sum_ty(builder, val, error_union_ty, error_ty)
    } else {
        None
    };

    match map_error(meta_tys, module, builder, func_writer, err_val) {
        Some(val) => {
            builder.ins().jump(finally_block, &[BlockArg::Value(val)]);
        }
        None => {
            builder.ins().jump(finally_block, &[]);
        }
    }

    builder.switch_to_block(finally_block);
    builder.seal_block(finally_block);

    if finally_ret.is_some() {
        Some(builder.block_params(finally_block)[0])
    } else {
        None
    }
}

fn tagged_union_has_discriminant(
    builder: &mut FunctionBuilder,
    tagged_union_ty: Intern<Ty>,
    val: Value,
    discrim: i64,
) -> Value {
    // todo: should absolute_ty be called?
    assert!(
        matches!(*tagged_union_ty, Ty::Enum { .. } | Ty::ErrorUnion { .. })
            || matches!(*tagged_union_ty, Ty::Optional { sub_ty } if !sub_ty.is_non_zero() ),
        "{tagged_union_ty:?} is not an enum/error union/aggregate optional"
    );
    assert!(tagged_union_ty.is_aggregate());

    let enum_layout = tagged_union_ty
        .enum_layout()
        .expect("we already checked that the type is an enum");

    let actual_discrim = builder.ins().load(
        types::I8,
        MemFlags::trusted(),
        val,
        enum_layout.discriminant_offset() as i32,
    );

    builder
        .ins()
        .icmp_imm(IntCC::Equal, actual_discrim, discrim)
}

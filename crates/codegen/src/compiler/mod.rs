pub mod comptime;
mod functions;
pub mod program;

use cranelift::codegen::{self, CodegenError};
use cranelift::prelude::{types, FunctionBuilder, FunctionBuilderContext, InstBuilder, Value};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError};
use hir_ty::ResolvedTy;
use interner::Interner;
use internment::Intern;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uid_gen::UIDGenerator;

use crate::mangle::Mangle;
use crate::{convert::*, CapyFnSignature, ComptimeToCompile};

use self::comptime::ComptimeResult;
use self::functions::FunctionCompiler;

pub(crate) struct LambdaToCompile {
    pub(crate) module_name: hir::FileName,
    pub(crate) lambda: Idx<hir::Lambda>,
    pub(crate) param_tys: Vec<Intern<ResolvedTy>>,
    pub(crate) return_ty: Intern<ResolvedTy>,
}

pub(crate) struct Compiler<'a> {
    pub(crate) verbose: bool,

    pub(crate) project_root: &'a std::path::Path,

    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: &'a FxHashMap<hir::FileName, hir::Bodies>,
    pub(crate) tys: &'a hir_ty::InferenceResult,

    pub(crate) builder_context: FunctionBuilderContext,
    pub(crate) ctx: codegen::Context,
    pub(crate) data_description: DataDescription,
    pub(crate) module: &'a mut dyn Module,
    pub(crate) pointer_ty: types::Type,

    // bodies to compile
    pub(crate) functions_to_compile: VecDeque<hir::Fqn>,
    pub(crate) lambdas_to_compile: VecDeque<LambdaToCompile>,

    // globals
    pub(crate) functions: FxHashMap<hir::Fqn, FuncId>,
    pub(crate) data: FxHashMap<hir::Fqn, DataId>,
    pub(crate) str_id_gen: UIDGenerator,
    pub(crate) comptime_results: &'a FxHashMap<ComptimeToCompile, ComptimeResult>,
}

impl Compiler<'_> {
    fn compile_queued_functions(&mut self) {
        while let Some(fqn) = self.functions_to_compile.pop_front() {
            let sig = self.tys[fqn]
                .as_function()
                .expect("tried to compile non-function as function");

            self.compile_real_function(sig, fqn);
        }
        while let Some(ltc) = self.lambdas_to_compile.pop_front() {
            self.compile_lambda(ltc);
        }
    }

    fn get_func_id(&mut self, fqn: hir::Fqn) -> FuncId {
        get_func_id(
            self.module,
            self.pointer_ty,
            self.project_root,
            &mut self.functions,
            &mut self.functions_to_compile,
            self.tys,
            self.interner,
            fqn,
        )
    }

    fn compile_lambda(&mut self, ltc: LambdaToCompile) {
        self.compile_function(
            &format!(
                "{}.lambda#{}",
                ltc.module_name.to_string(self.project_root, self.interner),
                ltc.lambda.into_raw()
            ),
            &ltc.to_mangled_name(self.project_root, self.interner),
            ltc.module_name,
            self.bodies_map[&ltc.module_name][ltc.lambda].body,
            ltc.param_tys,
            ltc.return_ty,
        );
    }

    fn compile_real_function(&mut self, sig: &CapyFnSignature, fqn: hir::Fqn) {
        if sig.is_extern {
            return;
        }

        self.compile_function(
            &fqn.to_string(self.project_root, self.interner),
            &fqn.to_mangled_name(self.project_root, self.interner),
            fqn.module,
            self.bodies_map[&fqn.module].function_body(fqn.name),
            sig.param_tys.clone(),
            sig.return_ty,
        );
    }

    fn compile_function(
        &mut self,
        unmangled_name: &str,
        mangled_name: &str,
        module_name: hir::FileName,
        body: Idx<hir::Expr>,
        param_tys: Vec<Intern<ResolvedTy>>,
        return_ty: Intern<ResolvedTy>,
    ) -> FuncId {
        let (comp_sig, new_idx_to_old_idx) =
            (param_tys.clone(), return_ty).to_cranelift_signature(self.module, self.pointer_ty);
        let func_id = self
            .module
            .declare_function(mangled_name, Linkage::Export, &comp_sig)
            .unwrap();

        self.ctx.func.signature = comp_sig.clone();

        // Create the builder to build a function.
        let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let compiler = FunctionCompiler {
            builder,
            module_name,
            project_root: self.project_root,
            signature: comp_sig,
            interner: self.interner,
            bodies_map: self.bodies_map,
            tys: self.tys,
            module: self.module,
            pointer_ty: self.pointer_ty,
            data_description: &mut self.data_description,
            functions_to_compile: &mut self.functions_to_compile,
            lambdas_to_compile: &mut self.lambdas_to_compile,
            local_functions: FxHashMap::default(),
            local_lambdas: FxHashMap::default(),
            functions: &mut self.functions,
            globals: &mut self.data,
            str_id_gen: &mut self.str_id_gen,
            comptime_results: self.comptime_results,
            var_id_gen: UIDGenerator::default(),
            locals: FxHashMap::default(),
            params: FxHashMap::default(),
        };

        compiler.finish(param_tys, return_ty, body, new_idx_to_old_idx);

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
    project_root: &std::path::Path,
    functions: &mut FxHashMap<hir::Fqn, FuncId>,
    functions_to_compile: &mut VecDeque<hir::Fqn>,
    tys: &hir_ty::InferenceResult,
    interner: &Interner,
    fqn: hir::Fqn,
) -> FuncId {
    if let Some(func_id) = functions.get(&fqn) {
        return *func_id;
    }

    functions_to_compile.push_back(fqn);

    let signature = tys[fqn]
        .as_function()
        .expect("tried to compile non-function as function");

    let (comp_sig, _) = signature.to_cranelift_signature(module, pointer_ty);

    let func_id = if signature.is_extern {
        module
            .declare_function(interner.lookup(fqn.name.0), Linkage::Import, &comp_sig)
            .expect("There are multiple extern functions with the same name")
    } else {
        module
            .declare_function(
                &fqn.to_mangled_name(project_root, interner),
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

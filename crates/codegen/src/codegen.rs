use inkwell::builder::{self, Builder};
use inkwell::context::Context;
use inkwell::data_layout::DataLayout;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::{Module, Linkage};
use inkwell::targets::FileType;
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, PointerType};
use inkwell::values::{
    AnyValue, BasicMetadataValueEnum, BasicValue, FunctionValue, IntValue, PointerValue, BasicValueEnum, IntMathValue,
};
use inkwell::{OptimizationLevel, AddressSpace, object_file};
use interner::Interner;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::ascii::escape_default;
use std::error::Error;
use std::str;
use std::path::{PathBuf, Path};
use std::fs;

pub(crate) struct CodeGen<'a, 'ctx> {
    pub(crate) context: &'ctx Context,
    pub(crate) module: &'a Module<'ctx>,
    pub(crate) current_builders: Vec<Builder<'ctx>>,
    pub(crate) functions_to_compile: Vec<hir::Fqn>,
    pub(crate) functions: FxHashMap<hir::Fqn, FunctionValue<'ctx>>,
    pub(crate) variables: FxHashMap<Idx<hir::LocalDef>, PointerValue<'ctx>>,
    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: FxHashMap<hir::Name, hir::Bodies>,
    pub(crate) types_map: FxHashMap<hir::Name, hir_types::InferenceResult>,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) current_functions: Vec<FunctionValue<'ctx>>,
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub(crate) fn finish(mut self) -> Result<Vec<u8>, String> {
        self.compile_queued_functions();

        Target::initialize_native(&InitializationConfig::default())
            .expect("Failed to initialize native target");

        // self.module.set_data_layout(&DataLayout::from("e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128"));

        self.module.set_source_file_name(&format!(
            "{}.{}", 
            self.module.get_source_file_name().to_str().unwrap(), 
            "capy"));

        let triple = TargetMachine::get_default_triple();
        self.module.set_triple(&triple);

        let cpu = TargetMachine::get_host_cpu_name().to_string();
        println!("{}", self
            .module
            .print_to_string()
            .to_string()
            .replacen(
                "target", 
                &format!("target cpu = \"{}\"\ntarget", cpu), 
                1));

        let cpu_features = TargetMachine::get_host_cpu_features().to_string();

        let target = Target::from_triple(&triple).unwrap();
        let target_machine = target
            .create_target_machine(
                &triple,
                &cpu,
                &cpu_features,
                OptimizationLevel::Aggressive,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .unwrap();

        println!("finalizing...");

        target_machine.write_to_file(self.module, FileType::Assembly, &Path::new("out/out.asm"));
        
        target_machine
            .write_to_memory_buffer(self.module, FileType::Object)
            .map_err(|message| {
                message.to_string()
            })
            .map(|buffer| buffer.as_slice().to_vec())
    }

    fn compile_queued_functions(&mut self) {
        while let Some(name) = self.functions_to_compile.pop() {
            self.compile_function(name);
            self.compile_queued_functions();
        }
    }

    #[inline]
    fn current_function(&self) -> &FunctionValue {
        self.current_functions.last().unwrap()
    }

    #[inline]
    fn string_type(&self) -> PointerType<'ctx> {
        self.context.i8_type().ptr_type(AddressSpace::default())
    }

    fn create_alloca<T: BasicType<'ctx>>(&self, type_: T, name: &str) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self
            .current_function()
            .get_first_basic_block()
            .unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(type_, name)
    }

    fn compile_function(&mut self, fqn: hir::Fqn) {
        let hir_def = self.world_index.get_definition(fqn).unwrap();

        let hir_function = match hir_def {
            hir::Definition::Function(f) => f,
            _ => panic!("tried to compile non-function as function"),
        };

        let param_types: Vec<BasicMetadataTypeEnum> = hir_function
            .params
            .iter()
            .filter_map(|param| match param.type_ {
                hir::Type::Unknown => unreachable!(),
                hir::Type::S32 => Some(self.context.i32_type().into()),
                hir::Type::String => Some(self.string_type().into()),
                hir::Type::Named(_) => todo!(),
                hir::Type::Void => None,
            })
            .collect();
        let param_types = param_types.as_slice();

        let fn_type = match hir_function.return_type {
            hir::Type::Unknown => unreachable!(),
            hir::Type::S32 => self.context.i32_type().fn_type(param_types, false),
            hir::Type::String => self.string_type().fn_type(param_types, false),
            hir::Type::Named(_) => todo!(),
            hir::Type::Void => self.context.void_type().fn_type(param_types, false),
        };

        let function = self
            .module
            .add_function(self.interner.lookup(fqn.name.0), fn_type, None);
        self.functions.insert(fqn, function);
        self.current_functions.push(function);

        let builder = self.context.create_builder();
        self.current_builders.push(builder);

        let entry_block = self.context.append_basic_block(function, "entry");

        self.current_builders.last().unwrap().position_at_end(entry_block);

        let hir_body = self.bodies_map[&fqn.module].function_body(fqn.name);

        match self.compile_expr(fqn.module, hir_body) {
            Some(body) => self.current_builders.last().unwrap().build_return(Some(&body)),
            None => self.current_builders.last().unwrap().build_return(None),
        };

        self.current_builders.pop();
        self.current_functions.pop();
    }

    fn compile_stmt(
        &mut self, 
        module: hir::Name, 
        stmt: &Idx<hir::Stmt>,
    ) {
        match self.bodies_map[&module][*stmt] {
            hir::Stmt::Expr(expr) => {
                match self.types_map[&module][expr] {
                    hir_types::ResolvedType::Unknown => unreachable!(),
                    hir_types::ResolvedType::S32 | hir_types::ResolvedType::String | hir_types::ResolvedType::Void => {
                        self.compile_expr(module, expr);
                    }
                    hir_types::ResolvedType::Named(_) => todo!(),
                };
            }
            hir::Stmt::LocalDef(local_def) => {
                let value = self.bodies_map[&module][local_def].value;

                let value = self.compile_expr(module, value).unwrap();

                let var = match self.types_map[&module][local_def] {
                    hir_types::ResolvedType::S32 => {
                        self.create_alloca(self.context.i32_type(), &format!("l{}", local_def.into_raw()))
                    }
                    hir_types::ResolvedType::String => {
                        self.create_alloca(self.string_type(), &format!("l{}", local_def.into_raw()))
                    }
                    hir_types::ResolvedType::Named(_) => todo!(),
                    _ => unreachable!(),
                };
                self.variables.insert(local_def, var);
                self.current_builders.last().unwrap().build_store(var, value);
            }
        }
    }

    fn compile_expr(
        &mut self,
        module: hir::Name,
        expr: Idx<hir::Expr>
    ) -> Option<BasicValueEnum<'ctx>> {
        match self.bodies_map[&module][expr].clone() {
            hir::Expr::IntLiteral(n) => Some(self.context.i32_type().const_int(n as u64, true).as_basic_value_enum()),
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs = self.compile_expr(module, lhs).unwrap().into_int_value();
                let rhs = self.compile_expr(module, rhs).unwrap().into_int_value();
                match op {
                    hir::BinaryOp::Add => 
                        Some(self.current_builders.last().unwrap().build_int_add(lhs, rhs, "tmp_add").as_basic_value_enum()),
                    hir::BinaryOp::Sub => 
                        Some(self.current_builders.last().unwrap().build_int_sub(lhs, rhs, "tmp_sub").as_basic_value_enum()),
                    hir::BinaryOp::Mul => 
                        Some(self.current_builders.last().unwrap().build_int_mul(lhs, rhs, "tmp_mul").as_basic_value_enum()),
                    hir::BinaryOp::Div => 
                        Some(self.current_builders.last().unwrap().build_int_signed_div(lhs, rhs, "tmp_div").as_basic_value_enum()),
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr = self.compile_expr(module, expr).unwrap().into_int_value();
                match op {
                    hir::UnaryOp::Pos => 
                        Some(expr.as_basic_value_enum()),
                    hir::UnaryOp::Neg => 
                        Some(self.current_builders.last().unwrap().build_int_neg(expr, "tmp_neg").as_basic_value_enum()),
                }
            }
            hir::Expr::StringLiteral(text) => {
                let builder = self.current_builders.last().unwrap();
                let global = builder.build_global_string_ptr(&text, ".str");
                global.set_linkage(Linkage::Internal);
                global.set_unnamed_addr(false);
                global.set_constant(true);

                Some(global.as_basic_value_enum())
            }
            hir::Expr::Call { path, args } => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let function = match self.functions.get(&fqn) {
                    Some(function) => function.clone(),
                    None => {
                        if self.interner.lookup(fqn.name.0) == "printf" {
                            let fn_type = self
                                .context
                                .void_type()
                                .fn_type(
                                    &[self.string_type().into()], 
                                    true);
                            let function = self.module.add_function(
                                "printf", 
                                fn_type, 
                                None);
                            self.functions.insert(fqn, function);
                            self.functions.get(&fqn).unwrap().clone()
                        } else {
                            self.compile_function(fqn);
                            self.functions.get(&fqn).unwrap().clone()
                        }
                    }
                };

                let mut argsv: Vec<BasicMetadataValueEnum> = Vec::with_capacity(args.len());

                for arg in args {
                    argsv.push(match self.types_map[&module][arg] {
                        hir_types::ResolvedType::Unknown => todo!(),
                        hir_types::ResolvedType::S32 | hir_types::ResolvedType::String => 
                            self.compile_expr(module, arg).unwrap().into(),
                        hir_types::ResolvedType::Named(_) => todo!(),
                        hir_types::ResolvedType::Void => todo!(),
                    });
                }

                self
                    .current_builders
                    .last()
                    .unwrap()
                    .build_call(function, argsv.as_slice(), "tmp_call")
                    .try_as_basic_value()
                    .left()
            }
            hir::Expr::Global(path) => todo!(),
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.compile_stmt(module, &stmt);
                }

                if let Some(val) = tail_expr {
                    self.compile_expr(module, val)
                } else {
                    None
                }
            }
            hir::Expr::Missing => todo!(),
            hir::Expr::Local(local_def) => {
                let var = self.variables.get(&local_def).unwrap();

                Some(self
                    .current_builders
                    .last()
                    .unwrap()
                    .build_load(*var, &format!("l{}_", local_def.into_raw())))
            }
            hir::Expr::Param { idx } => Some(self
                .current_functions
                .last()
                .unwrap()
                .get_nth_param(idx)
                .unwrap()),
        }
    }
}
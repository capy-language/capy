use inkwell::builder::{self, Builder};
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::targets::FileType;
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, PointerType};
use inkwell::values::{
    AnyValue, BasicMetadataValueEnum, BasicValue, FunctionValue, IntValue, PointerValue,
};
use inkwell::{OptimizationLevel, AddressSpace};
use interner::Interner;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::ascii::escape_default;
use std::error::Error;
use std::str;

pub(crate) struct CodeGen<'a, 'ctx> {
    pub(crate) context: &'ctx Context,
    pub(crate) module: &'a Module<'ctx>,
    pub(crate) builders: Vec<Builder<'ctx>>,
    pub(crate) functions_to_compile: Vec<hir::Fqn>,
    pub(crate) functions: FxHashMap<hir::Fqn, FunctionValue<'ctx>>,
    pub(crate) variables: FxHashMap<Idx<hir::LocalDef>, PointerValue<'ctx>>,
    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: FxHashMap<hir::Name, hir::Bodies>,
    pub(crate) types_map: FxHashMap<hir::Name, hir_types::InferenceResult>,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) current_function: Vec<FunctionValue<'ctx>>,
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub(crate) fn finish(mut self) -> Vec<u8> {
        self.compile_queued_functions();

        Target::initialize_native(&InitializationConfig::default())
            .expect("Failed to initialize native target");

        let triple = TargetMachine::get_default_triple();
        println!("triple: {}", triple);
        let cpu = TargetMachine::get_host_cpu_name().to_string();
        println!("cpu: {}", cpu);
        let features = TargetMachine::get_host_cpu_features().to_string();
        println!("features: {}\n", features);
        println!("{}", self.module.print_to_string().to_string());

        let target = Target::from_triple(&triple).unwrap();
        let machine = target
            .create_target_machine(
                &triple,
                &cpu,
                &features,
                OptimizationLevel::None,
                RelocMode::Default,
                CodeModel::Default,
            )
            .unwrap();

        println!("asm to memory buffer");
        let out = machine
            .write_to_memory_buffer(&self.module, FileType::Assembly)
            .unwrap();
        let out = out.as_slice();
        print!("\n{}\n", String::from_utf8_lossy(out));

        Vec::new()
    }

    fn compile_queued_functions(&mut self) {
        while let Some(name) = self.functions_to_compile.pop() {
            self.compile_function(name);
            self.compile_queued_functions();
        }
    }

    #[inline]
    fn current_function(&self) -> &FunctionValue {
        self.current_function.last().unwrap()
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
        self.current_function.push(function);

        let builder = self.context.create_builder();
        self.builders.push(builder);

        let entry_block = self.context.append_basic_block(function, "entry");

        self.builders.last().unwrap().position_at_end(entry_block);

        let hir_body = self.bodies_map[&fqn.module].function_body(fqn.name);

        match hir_function.return_type {
            hir::Type::Unknown => unreachable!(),
            hir::Type::S32 => {
                let body = self.compile_int_expr(fqn.module, hir_body);
                self.builders.last().unwrap().build_return(Some(&body));
            },
            hir::Type::String => {
                let body = self.compile_string_expr(fqn.module, hir_body);
                self.builders.last().unwrap().build_return(Some(&body));
            },
            hir::Type::Named(_) => todo!(),
            hir::Type::Void => {
                let body = self.compile_int_expr(fqn.module, hir_body);
                self.builders.last().unwrap().build_return(Some(&body));
            },
        };

        self.builders.pop();
        self.current_function.pop();
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
                    hir_types::ResolvedType::S32 => { 
                        self.compile_int_expr(module, expr);
                    }
                    hir_types::ResolvedType::String => {
                        self.compile_string_expr(module, expr);
                    }
                    hir_types::ResolvedType::Named(_) => todo!(),
                    hir_types::ResolvedType::Void => todo!(),
                };
            }
            hir::Stmt::LocalDef(local_def) => {
                let value = self.bodies_map[&module][local_def].value;

                match self.types_map[&module][local_def] {
                    hir_types::ResolvedType::S32 => {
                        let value = self.compile_int_expr(module, value);
                        
                        let var = self.create_alloca(self.context.i32_type(), &format!("l{}", local_def.into_raw()));
                        self.variables.insert(local_def, var);
                        
                        self.builders.last().unwrap().build_store(var, value);
                    },
                    hir_types::ResolvedType::String => {
                        let value = self.compile_string_expr(module, value);
                        
                        let var = self.create_alloca(self.context.i32_type(), &format!("l{}", local_def.into_raw()));
                        self.variables.insert(local_def, var);
                        
                        self.builders.last().unwrap().build_store(var, value);
                    },
                    hir_types::ResolvedType::Named(_) => todo!(),
                    _ => unreachable!(),
                };
            }
        }
    }

    fn compile_int_expr(
        &mut self,
        module: hir::Name,
        expr: Idx<hir::Expr>
    ) -> IntValue<'ctx> {
        match self.bodies_map[&module][expr].clone() {
            hir::Expr::IntLiteral(n) => self.context.i32_type().const_int(n as u64, true),
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs = self.compile_int_expr(module, lhs);
                let rhs = self.compile_int_expr(module, rhs);
                match op {
                    hir::BinaryOp::Add => self.builders.last().unwrap().build_int_add(lhs, rhs, "tmp_add"),
                    hir::BinaryOp::Sub => self.builders.last().unwrap().build_int_sub(lhs, rhs, "tmp_sub"),
                    hir::BinaryOp::Mul => self.builders.last().unwrap().build_int_mul(lhs, rhs, "tmp_mul"),
                    hir::BinaryOp::Div => self.builders.last().unwrap().build_int_signed_div(lhs, rhs, "tmp_div"),
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr = self.compile_int_expr(module, expr).to_owned();
                match op {
                    hir::UnaryOp::Pos => expr,
                    hir::UnaryOp::Neg => self.builders.last().unwrap().build_int_neg(expr, "tmp_neg"),
                }
            }
            hir::Expr::Call { path, args } => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let name = self.interner.lookup(fqn.name.0);
                let function = match self.functions.get(&fqn) {
                    Some(function) => function.clone(),
                    None => {
                        self.compile_function(fqn);
                        self.functions.get(&fqn).unwrap().clone()
                    }
                };

                let mut argsv: Vec<BasicMetadataValueEnum> = Vec::with_capacity(args.len());

                for arg in args {
                    argsv.push(match self.types_map[&module][arg] {
                        hir_types::ResolvedType::Unknown => todo!(),
                        hir_types::ResolvedType::S32 => self.compile_int_expr(module, arg).into(),
                        hir_types::ResolvedType::String => self.compile_string_expr(module, arg).into(),
                        hir_types::ResolvedType::Named(_) => todo!(),
                        hir_types::ResolvedType::Void => todo!(),
                    });
                }

                match self
                    .builders
                    .last()
                    .unwrap()
                    .build_call(function, argsv.as_slice(), "tmp_call")
                    .try_as_basic_value()
                    .left()
                {
                    Some(value) => value.into_int_value(),
                    None => unreachable!(),
                }
            }
            hir::Expr::Global(path) => todo!(),
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.compile_stmt(module, &stmt);
                }

                if let Some(val) = tail_expr {
                    self.compile_int_expr(module, val)
                } else {
                    unreachable!()
                }
            }
            hir::Expr::Missing => todo!(),
            hir::Expr::StringLiteral(_) => todo!(),
            hir::Expr::Local(local_def) => {
                let var = self.variables.get(&local_def).unwrap();

                self
                    .builders
                    .last()
                    .unwrap()
                    .build_load(*var, &format!("l{}_", local_def.into_raw()))
                    .into_int_value()
            }
            hir::Expr::Param { idx } => self
                .current_function
                .last()
                .unwrap()
                .get_nth_param(idx)
                .unwrap()
                .into_int_value(),
        }
    }

    fn compile_string_expr(
        &mut self,
        module: hir::Name,
        expr: Idx<hir::Expr>
    ) -> PointerValue<'ctx> {
        match self.bodies_map[&module][expr].clone() {
            hir::Expr::Call { path, args } => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                let name = self.interner.lookup(fqn.name.0);
                let function = match self.functions.get(&fqn) {
                    Some(function) => function.clone(),
                    None => {
                        self.compile_function(fqn);
                        self.functions.get(&fqn).unwrap().clone()
                    }
                };

                let mut argsv: Vec<BasicMetadataValueEnum> = Vec::with_capacity(args.len());

                for arg in args {
                    argsv.push(match self.types_map[&module][arg] {
                        hir_types::ResolvedType::Unknown => todo!(),
                        hir_types::ResolvedType::S32 => self.compile_int_expr(module, arg).into(),
                        hir_types::ResolvedType::String => self.compile_string_expr(module, arg).into(),
                        hir_types::ResolvedType::Named(_) => todo!(),
                        hir_types::ResolvedType::Void => todo!(),
                    });
                }

                match self
                    .builders
                    .last()
                    .unwrap()
                    .build_call(function, argsv.as_slice(), "tmp_call")
                    .try_as_basic_value()
                    .left()
                {
                    Some(value) => value.into_pointer_value(),
                    None => unreachable!(),
                }
            }
            hir::Expr::Global(path) => todo!(),
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.compile_stmt(module, &stmt);
                }

                if let Some(val) = tail_expr {
                    self.compile_string_expr(module, val)
                } else {
                    unreachable!()
                }
            }
            hir::Expr::Missing => todo!(),
            hir::Expr::StringLiteral(text) => {
                unsafe { self.builders.last().unwrap().build_global_string(&text, "tmp_str") }
                    .as_pointer_value()
            },
            hir::Expr::Local(local_def) => {
                let var = self.variables.get(&local_def).unwrap();

                self
                    .builders
                    .last()
                    .unwrap()
                    .build_load(*var, &format!("l{}_", local_def.into_raw()))
                    .into_pointer_value()
            }
            hir::Expr::Param { idx } => self
                .current_function
                .last()
                .unwrap()
                .get_nth_param(idx)
                .unwrap()
                .into_pointer_value(),
            hir::Expr::IntLiteral(_) => todo!(),
            hir::Expr::Binary { lhs, rhs, op } => todo!(),
            hir::Expr::Unary { expr, op } => todo!(),
        }
    }

}

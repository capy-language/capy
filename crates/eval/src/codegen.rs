use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType};
use inkwell::values::{
    AnyValue, BasicMetadataValueEnum, BasicValue, FunctionValue, IntValue, PointerValue,
};
use inkwell::OptimizationLevel;
use interner::Interner;
use la_arena::Idx;
use rustc_hash::FxHashMap;
use std::error::Error;

/// Convenience type alias for the `sum` function.
///
/// Calling this is innately `unsafe` because there's no guarantee it doesn't
/// do `unsafe` operations internally.
type MainFunc = unsafe extern "C" fn();

pub(crate) struct CodeGen<'a, 'ctx> {
    pub(crate) context: &'ctx Context,
    pub(crate) module: &'a Module<'ctx>,
    pub(crate) builder: &'a Builder<'ctx>,
    pub(crate) functions_to_compile: Vec<hir::Fqn>,
    pub(crate) variables: FxHashMap<Idx<hir::LocalDef>, PointerValue<'ctx>>,
    pub(crate) interner: &'a Interner,
    pub(crate) bodies_map: FxHashMap<hir::Name, hir::Bodies>,
    pub(crate) types_map: FxHashMap<hir::Name, hir_types::InferenceResult>,
    pub(crate) world_index: &'a hir::WorldIndex,
    pub(crate) current_function: Option<FunctionValue<'ctx>>
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {

    pub(crate) fn finish(mut self) -> Vec<u8> {
        self.compile_queued_functions();

        Vec::new()
    }

    fn compile_queued_functions(&mut self) {
        while let Some(name) = self.functions_to_compile.pop() {
            self.compile_function(name);
            self.compile_queued_functions();
        }
    }

    fn create_alloca<T: BasicType<'ctx>>(&self, type_: T, name: &str) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();

        let entry = self.current_function.unwrap().get_first_basic_block().unwrap();

        match entry.get_first_instruction() {
            Some(first_instr) => builder.position_before(&first_instr),
            None => builder.position_at_end(entry),
        }

        builder.build_alloca(type_, name)
    }

    fn compile_sum(&self) {
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        let function = self.module.add_function("sum", fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(basic_block);

        let x = function.get_nth_param(0).unwrap().into_int_value();
        let y = function.get_nth_param(1).unwrap().into_int_value();
        let z = function.get_nth_param(2).unwrap().into_int_value();

        let sum = self.builder.build_int_add(x, y, "sum");
        let sum = self.builder.build_int_add(sum, z, "sum");

        self.builder.build_return(Some(&sum));

        println!(
            "Generated LLVM IR: {}",
            function.print_to_string().to_string()
        );
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
                hir::Type::String => todo!(),
                hir::Type::Named(_) => todo!(),
                hir::Type::Void => None,
            })
            .collect();
        let param_types = param_types.as_slice();

        let fn_type = match hir_function.return_type {
            hir::Type::Unknown => unreachable!(),
            hir::Type::S32 => self.context.i32_type().fn_type(param_types, false),
            hir::Type::String => self.context.i32_type().fn_type(param_types, false),
            hir::Type::Named(_) => todo!(),
            hir::Type::Void => self.context.void_type().fn_type(param_types, false),
        };

        let function = self
            .module
            .add_function(self.interner.lookup(fqn.name.0), fn_type, None);
        self.current_function = Some(function);

        let entry_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(entry_block);

        let hir_body = self.bodies_map[&fqn.module].function_body(fqn.name);

        let body = self.compile_int_expr(fqn.module, hir_body);

        self.builder.build_return(Some(&body));

        self.current_function = None;

        println!(
            "Generated LLVM IR: \n{}",
            function.clone().print_to_string().to_string()
        );
    }

    fn compile_stmt(&mut self, module: hir::Name, stmt: &Idx<hir::Stmt>) {
        match self.bodies_map[&module][*stmt] {
            hir::Stmt::Expr(expr) => { self.compile_int_expr(module, expr); },
            hir::Stmt::LocalDef(local_def) => {
                let value = self.bodies_map[&module][local_def].value;

                let (value, type_) = match self.types_map[&module][local_def] {
                    hir_types::ResolvedType::S32 => (
                        self.compile_int_expr(module, value),
                        self.context.i32_type(),
                    ),
                    hir_types::ResolvedType::String => todo!(),
                    hir_types::ResolvedType::Named(_) => todo!(),
                    _ => unreachable!(),
                };

                let var = self
                    .create_alloca(type_, &format!("l{}", local_def.into_raw()));

                self.variables.insert(local_def, var);

                self.builder.build_store(var, value);
            }
        }
    }

    fn compile_int_expr(&mut self, module: hir::Name, expr: Idx<hir::Expr>) -> IntValue<'ctx> {
        match self.bodies_map[&module][expr].clone() {
            hir::Expr::IntLiteral(n) => self.context.i32_type().const_int(n as u64, true),
            hir::Expr::Binary { lhs, rhs, op } => {
                let lhs = self.compile_int_expr(module, lhs);
                let rhs = self.compile_int_expr(module, rhs);
                match op {
                    hir::BinaryOp::Add => self.builder.build_int_add(lhs, rhs, "tmp_add"),
                    hir::BinaryOp::Sub => self.builder.build_int_sub(lhs, rhs, "tmp_sub"),
                    hir::BinaryOp::Mul => self.builder.build_int_mul(lhs, rhs, "tmp_mul"),
                    hir::BinaryOp::Div => self.builder.build_int_signed_div(lhs, rhs, "tmp_div"),
                }
            }
            hir::Expr::Unary { expr, op } => {
                let expr = self.compile_int_expr(module, expr).to_owned();
                match op {
                    hir::UnaryOp::Pos => expr,
                    hir::UnaryOp::Neg => self.builder.build_int_neg(expr, "tmp_neg"),
                }
            }
            hir::Expr::Call { path, .. } => {
                let fqn = match path {
                    hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                    hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                };

                self.functions_to_compile.push(fqn);

                let name = self.interner.lookup(fqn.name.0);
                let function = self
                    .module
                    .get_function(name)
                    .expect(&format!("the function `{name}` wasn't generated yet"));

                let arg_types: Vec<BasicMetadataValueEnum> = function
                    .get_param_iter()
                    .map(|param| param.into())
                    .collect();
                let arg_types = arg_types.as_slice();

                match self
                    .builder
                    .build_call(function, arg_types, "tmp_call")
                    .try_as_basic_value()
                    .left()
                {
                    Some(value) => value.into_int_value(),
                    None => unreachable!(),
                }
            }
            hir::Expr::Global(path) => {
                // let fqn = match path {
                //     hir::PathWithRange::ThisModule { name, .. } => hir::Fqn { module, name },
                //     hir::PathWithRange::OtherModule { fqn, .. } => fqn,
                // };

                // let var = self.variables.get(&fqn.name).unwrap();

                // self.builder
                //     .build_load(*var, self.interner.lookup(fqn.name.0))
                //     .into_int_value()
                todo!()
            }
            hir::Expr::Block { stmts, tail_expr } => {
                for stmt in stmts {
                    self.compile_stmt(module, &stmt);
                }

                if let Some(val) = tail_expr {
                    self.compile_int_expr(module, val)
                } else {
                    self.context.i32_type().const_int(0, true)
                }
            }
            hir::Expr::Missing => todo!(),
            hir::Expr::StringLiteral(_) => todo!(),
            hir::Expr::Local(local_def) => {
                let var = self.variables.get(&local_def).unwrap();

                self.builder
                    .build_load(*var, &format!("l{}_", local_def.into_raw()))
                    .into_int_value()
            },
            hir::Expr::Param { idx } => {
                self.current_function.unwrap().get_nth_param(idx).unwrap().into_int_value()
            },
        }
    }
}

pub(crate) fn eval() -> Result<(), Box<dyn Error>> {
    let context = Context::create();
    let module = context.create_module("sum");
    let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;
    // let codegen = CodeGen {
    //     context: &context,
    //     module,
    //     builder: context.create_builder(),
    //     execution_engine,
    // };

    // let sum = codegen.jit_compile_sum().ok_or("Unable to JIT compile `sum`")?;

    // let x = 4u64;
    // let y = 5u64;
    // let z = 6u64;

    // unsafe {
    //     println!("{} + {} + {} = {}", x, y, z, sum.call(x, y, z));
    //     assert_eq!(sum.call(x, y, z), x + y + z);
    // }

    Ok(())
}

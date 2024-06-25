use cranelift::{
    codegen::{
        entity::EntityRef,
        ir::{
            AbiParam, ArgumentPurpose, Inst, InstBuilder, MemFlags, Signature, StackSlotData,
            StackSlotKind, Type, Value,
        },
        isa::CallConv,
    },
    frontend::{FunctionBuilder, Variable},
};
use hir_ty::Ty;
use internment::Intern;
use la_arena::Idx;

use crate::{
    compiler::{functions::FunctionCompiler, MemoryLoc},
    layout::GetLayoutInfo,
};

pub mod aarch64;
pub mod x86_64;

#[derive(Clone, Copy, Debug)]
pub enum Abi {
    X64,
}

impl Abi {
    pub fn fn_to_target(&self, func_ty: (&Vec<Intern<Ty>>, Intern<Ty>)) -> FnAbi {
        match self {
            Abi::X64 => x86_64::fn_ty_to_abi(func_ty),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PassMode {
    Cast {
        lo: Type,
        hi: Option<Type>,
        orig: Intern<Ty>,
    },
    Direct(Type),
    Indirect(Option<usize>),
}

impl PassMode {
    #[inline]
    pub fn cast((lo, hi): (Type, Option<Type>), orig: Intern<Ty>) -> Self {
        Self::Cast { lo, hi, orig }
    }
    #[inline]
    pub fn direct(ty: Type) -> Self {
        Self::Direct(ty)
    }
    #[inline]
    pub fn indirect_by_val(size: usize) -> Self {
        Self::Indirect(Some(size))
    }
    #[inline]
    pub fn indiret() -> Self {
        Self::Indirect(None)
    }
    #[inline]
    pub fn is_indirect(&self) -> bool {
        matches!(self, PassMode::Indirect(_))
    }
    // TODO: small vector optimization
    #[inline]
    pub fn to_abiparam(&self, ptr_ty: Type) -> Vec<AbiParam> {
        match self {
            PassMode::Cast { lo, hi, .. } => {
                let mut params = vec![AbiParam::new(*lo)];
                if let Some(hi) = hi {
                    params.push(AbiParam::new(*hi));
                }
                params
            }
            PassMode::Direct(ty) => vec![AbiParam::new(*ty)],
            PassMode::Indirect(Some(sz)) => vec![AbiParam::special(
                ptr_ty,
                ArgumentPurpose::StructArgument(*sz as u32),
            )],
            PassMode::Indirect(None) => vec![AbiParam::new(ptr_ty)],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnAbi {
    args: Vec<(PassMode, u16)>,
    ret: Option<PassMode>,
}

impl FnAbi {
    pub fn new() -> Self {
        Self {
            args: vec![],
            ret: None,
        }
    }
    pub fn to_cl(&self, ptr_ty: Type) -> Signature {
        // TODO: actually use the correct calling convention here
        let mut sig = Signature::new(CallConv::SystemV);
        if let Some(ret) = self.ret {
            if ret.is_indirect() {
                sig.params
                    .push(AbiParam::special(ptr_ty, ArgumentPurpose::StructReturn))
            } else {
                sig.returns.append(&mut ret.to_abiparam(ptr_ty));
            }
        }

        for (arg, _) in &self.args {
            sig.params.append(&mut arg.to_abiparam(ptr_ty));
        }

        sig
    }

    pub fn get_arg_list(&self, args: Vec<Value>, func_cmplr: &mut FunctionCompiler) -> Vec<Value> {
        let mut arg_list = vec![];

        for (pass, idx) in &self.args {
            let arg = args[*idx as usize];
            match pass {
                PassMode::Cast { lo, hi, .. } => {
                    let lo = func_cmplr
                        .builder
                        .ins()
                        .load(*lo, MemFlags::trusted(), arg, 0);
                    arg_list.push(lo);
                    if let Some(hi) = *hi {
                        let hi = func_cmplr
                            .builder
                            .ins()
                            .load(hi, MemFlags::trusted(), arg, 8);
                        arg_list.push(hi);
                    }
                }
                _ => arg_list.push(arg),
            }
        }
        arg_list
    }

    pub fn ret_addr(
        &self,
        args: &mut Vec<Value>,
        builder: &mut FunctionBuilder,
        return_ty: Intern<Ty>,
        ptr_ty: Type,
    ) -> Option<Value> {
        if let Some(PassMode::Indirect(_)) = self.ret {
            let stack_slot = builder.create_sized_stack_slot(StackSlotData {
                kind: StackSlotKind::ExplicitSlot,
                size: return_ty.size(),
                align_shift: return_ty.align() as u8,
            });
            let stack_slot_addr = builder.ins().stack_addr(ptr_ty, stack_slot, 0);

            args.insert(0, stack_slot_addr);
            Some(stack_slot_addr)
        } else {
            None
        }
    }

    pub fn handle_ret(
        &self,
        call: Inst,
        func_cmplr: &mut FunctionCompiler,
        ret_slot: Option<Value>,
    ) -> Option<Value> {
        if let Some(ret_slot) = ret_slot {
            return Some(ret_slot);
        }
        match self.ret? {
            PassMode::Cast { hi, orig, .. } => {
                let slot = func_cmplr.builder.create_sized_stack_slot(StackSlotData {
                    kind: StackSlotKind::ExplicitSlot,
                    size: orig.size(),
                    align_shift: orig.align().trailing_zeros() as u8,
                });
                let lo = func_cmplr.builder.inst_results(call)[0];
                func_cmplr.builder.ins().stack_store(lo, slot, 0);
                if let Some(_) = hi {
                    let hi = func_cmplr.builder.inst_results(call)[1];
                    func_cmplr.builder.ins().stack_store(hi, slot, 8);
                }

                Some(
                    func_cmplr
                        .builder
                        .ins()
                        .stack_addr(func_cmplr.ptr_ty, slot, 0),
                )
            }
            PassMode::Direct(_) => {
                let rets = func_cmplr.builder.inst_results(call);
                Some(rets[0])
            }
            PassMode::Indirect(_) => unreachable!("indirect return without stack address"),
        }
    }

    pub fn build_fn(
        &self,
        func_cmplr: &mut FunctionCompiler,
        return_ty: Intern<Ty>,
        function_body: Idx<hir::Expr>,
    ) {
        // Create the entry block, to start emitting code in.
        let entry_block = func_cmplr.builder.create_block();

        func_cmplr
            .builder
            .append_block_params_for_function_params(entry_block);

        func_cmplr.builder.switch_to_block(entry_block);
        func_cmplr.builder.seal_block(entry_block);
        let mut ret = 0;
        if let Some(PassMode::Indirect(_)) = self.ret {
            ret += 1
        }
        let mut idx_off = 0;
        for (arg, idx) in &self.args {
            let param = ret + *idx + idx_off;

            let var = Variable::new(func_cmplr.var_id_gen.generate_unique_id() as usize);
            func_cmplr.params.insert(*idx as u64, var);
            let (val, val_ty) = match arg {
                PassMode::Cast { hi, orig, .. } => {
                    let stack_slot = func_cmplr.builder.create_sized_stack_slot(StackSlotData {
                        kind: StackSlotKind::ExplicitSlot,
                        size: orig.size(),
                        align_shift: orig.align().trailing_zeros() as u8,
                    });
                    let val = func_cmplr.builder.block_params(entry_block)[param as usize];
                    func_cmplr.builder.ins().stack_store(val, stack_slot, 0);
                    if let Some(_) = hi {
                        let val = func_cmplr.builder.block_params(entry_block)[1 + param as usize];
                        func_cmplr.builder.ins().stack_store(val, stack_slot, 8);
                        idx_off += 1;
                    }
                    (
                        func_cmplr
                            .builder
                            .ins()
                            .stack_addr(func_cmplr.ptr_ty, stack_slot, 0),
                        func_cmplr.ptr_ty,
                    )
                }
                PassMode::Direct(ty) => (
                    func_cmplr.builder.block_params(entry_block)[param as usize],
                    *ty,
                ),
                PassMode::Indirect(sz) => {
                    // TODO: handle structs not on the stack
                    let sz = sz.unwrap();
                    let stack_slot = func_cmplr.builder.create_sized_stack_slot(StackSlotData {
                        kind: StackSlotKind::ExplicitSlot,
                        size: sz as u32,
                        align_shift: 3,
                    });
                    let ptr = func_cmplr.builder.block_params(entry_block)[param as usize];
                    // be very explicit to cranelift what we are doing here
                    // since there is no `emit_stack_memcpy`, do it ourselves
                    // TODO: move this code to where it is actually needs
                    let mut off = 0;
                    macro_rules! mem_cpy_loop {
                        ($width:expr) => {
                            while (off + $width) <= (sz as i32 / $width) * $width {
                                let bytes = func_cmplr.builder.ins().load(
                                    Type::int_with_byte_size($width).unwrap(),
                                    MemFlags::trusted(),
                                    ptr,
                                    off,
                                );
                                func_cmplr.builder.ins().stack_store(bytes, stack_slot, off);
                                off += $width;
                            }
                        };
                    }
                    mem_cpy_loop!(8);
                    mem_cpy_loop!(4);
                    mem_cpy_loop!(2);
                    mem_cpy_loop!(1);

                    (
                        func_cmplr
                            .builder
                            .ins()
                            .stack_addr(func_cmplr.ptr_ty, stack_slot, 0),
                        func_cmplr.ptr_ty,
                    )
                }
            };
            func_cmplr.builder.declare_var(var, val_ty);

            func_cmplr.builder.def_var(var, val);
        }

        if let Some(ret) = self.ret {
            match ret {
                PassMode::Cast { lo, hi, orig } => {
                    let slot = func_cmplr.builder.create_sized_stack_slot(StackSlotData {
                        kind: StackSlotKind::ExplicitSlot,
                        size: orig.size() as u32,
                        align_shift: orig.align().trailing_zeros() as u8,
                    });
                    let tmp_mem = MemoryLoc::from_stack(slot, 0);
                    func_cmplr.compile_and_cast_into_memory(function_body, return_ty, tmp_mem);
                    let mut rets = vec![func_cmplr.builder.ins().stack_load(lo, slot, 0)];
                    if let Some(rethi) = hi {
                        rets.push(func_cmplr.builder.ins().stack_load(rethi, slot, 8));
                    }

                    func_cmplr.builder.ins().return_(&rets);
                }
                PassMode::Direct(_) => {
                    if let Some(val) = func_cmplr.compile_and_cast(function_body, return_ty) {
                        func_cmplr.builder.ins().return_(&[val]);
                    } else {
                        func_cmplr.builder.ins().return_(&[]);
                    }
                }
                PassMode::Indirect(_) => {
                    let ret_addr = func_cmplr.builder.block_params(entry_block)[0 as usize];
                    let tmp_mem = MemoryLoc::from_addr(ret_addr, 0);
                    func_cmplr.compile_and_cast_into_memory(function_body, return_ty, tmp_mem);
                    func_cmplr.builder.ins().return_(&[]);
                }
            }
        } else {
            func_cmplr.compile_and_cast(function_body, return_ty);
            func_cmplr.builder.ins().return_(&[]);
        }
        func_cmplr.builder.seal_all_blocks();
    }
}

use std::{
    borrow::Cow,
    fmt::{self, Display, Write},
    ops::{Index, IndexMut},
};

use cranelift::{
    codegen::{
        entity::{ListPool, SecondaryMap},
        ir::{BlockCall, Function, InstructionData},
        write::FuncWriter,
    },
    prelude::{Block, Value},
};

// todo: replace all u0:0 function calls within a function with the actual name of the function being referred to

/// The default `PlainFuncWriter` included in cranelift isn't very good.
/// All blocks are just printed `block0`, `block1`, `block2`, etc.
///
/// When debugging the cranelift output of a very long function, this can be very annoying.
///
/// This is a custom implementation of `cranelift::codegen::write::FuncWriter` which gives each
/// block its own name.
///
/// Block names are inserted by doing something like this:
/// ```compile_fail
/// let func_w = NiceFuncWriter::default();
///
/// func_w[exit_block] = "exit".into();
/// ```
#[derive(Default)]
pub(crate) struct NiceFuncWriter {
    block_names: SecondaryMap<Block, Cow<'static, str>>,
}

impl NiceFuncWriter {
    fn display_block(&self, block: Block) -> NamedBlockDisplay {
        NamedBlockDisplay {
            block,
            name: self.block_names.get(block).filter(|n| !n.is_empty()),
        }
    }
}

impl Index<Block> for NiceFuncWriter {
    type Output = Cow<'static, str>;

    fn index(&self, index: Block) -> &Self::Output {
        &self.block_names[index]
    }
}

impl IndexMut<Block> for NiceFuncWriter {
    fn index_mut(&mut self, index: Block) -> &mut Self::Output {
        &mut self.block_names[index]
    }
}

impl FuncWriter for NiceFuncWriter {
    fn write_block_header(
        &mut self,
        w: &mut dyn std::fmt::Write,
        func: &cranelift::codegen::ir::Function,
        block: cranelift::prelude::Block,
        indent: usize,
    ) -> core::fmt::Result {
        let cold = if func.layout.is_cold(block) {
            " cold"
        } else {
            ""
        };

        // The `indent` is the instruction indentation. block headers are 4 spaces out from that.
        write!(w, "{1:0$}", indent - 4, "")?;
        write!(w, "{}", self.display_block(block))?;

        let mut args = func.dfg.block_params(block).iter().cloned();
        match args.next() {
            None => return writeln!(w, "{cold}:"),
            Some(arg) => {
                write!(w, "(")?;
                write_arg(w, func, arg)?;
            }
        }
        // Remaining arguments.
        for arg in args {
            write!(w, ", ")?;
            write_arg(w, func, arg)?;
        }
        writeln!(w, "){cold}:")
    }

    fn write_instruction(
        &mut self,
        w: &mut dyn std::fmt::Write,
        func: &cranelift::codegen::ir::Function,
        aliases: &cranelift::codegen::entity::SecondaryMap<
            cranelift::prelude::Value,
            Vec<cranelift::prelude::Value>,
        >,
        inst: cranelift::codegen::ir::Inst,
        indent: usize,
    ) -> core::fmt::Result {
        let pool = &func.dfg.value_lists;
        let jump_tables = &func.dfg.jump_tables;
        match func.dfg.insts[inst] {
            InstructionData::Jump {
                opcode,
                destination,
            } => {
                let mut s = String::with_capacity(16);
                // Source location goes first.
                let srcloc = func.srcloc(inst);
                if !srcloc.is_default() {
                    write!(s, "{srcloc} ")?;
                }

                // Write out prefix and indent the instruction.
                write!(w, "{s:indent$}")?;

                assert!(func.dfg.inst_results(inst).is_empty());

                write!(w, "{opcode} ")?;
                write_block_call(w, self, destination, pool)?;
                writeln!(w)?;
            }
            InstructionData::Brif {
                opcode,
                arg,
                blocks,
            } => {
                let mut s = String::with_capacity(16);
                // Source location goes first.
                let srcloc = func.srcloc(inst);
                if !srcloc.is_default() {
                    write!(s, "{srcloc} ")?;
                }

                // Write out prefix and indent the instruction.
                write!(w, "{s:indent$}")?;

                assert!(func.dfg.inst_results(inst).is_empty());

                write!(w, "{opcode} ")?;

                let [block_then, block_else] = blocks;

                write!(w, " {arg}, ")?;
                write_block_call(w, self, block_then, pool)?;
                write!(w, ", ")?;
                write_block_call(w, self, block_else, pool)?;
                writeln!(w)?;
            }
            InstructionData::BranchTable { opcode, arg, table } => {
                let mut s = String::with_capacity(16);
                // Source location goes first.
                let srcloc = func.srcloc(inst);
                if !srcloc.is_default() {
                    write!(s, "{srcloc} ")?;
                }

                // Write out prefix and indent the instruction.
                write!(w, "{s:indent$}")?;

                assert!(func.dfg.inst_results(inst).is_empty());

                write!(w, "{opcode} ")?;

                write!(w, " {arg}, ")?;

                let jt = &jump_tables[table];
                write_block_call(w, self, jt.default_block(), pool)?;
                write!(w, ", [")?;
                if let Some((first, rest)) = jt.as_slice().split_first() {
                    write_block_call(w, self, *first, pool)?;
                    for block in rest {
                        write!(w, ", ")?;
                        write_block_call(w, self, *block, pool)?;
                    }
                }
                writeln!(w, "]")?;
            }
            _ => {
                cranelift::codegen::write::PlainWriter
                    .write_instruction(w, func, aliases, inst, indent)?;
            }
        }

        Ok(())
    }
}

fn write_block_call(
    w: &mut dyn std::fmt::Write,
    func_w: &NiceFuncWriter,
    block: BlockCall,
    pool: &ListPool<Value>,
) -> fmt::Result {
    write!(w, "{}", func_w.display_block(block.block(pool)))?;
    if block.len(pool) > 0 {
        write!(w, "(")?;
        for (ix, arg) in block.args(pool).enumerate() {
            if ix > 0 {
                write!(w, ", ")?;
            }
            write!(w, "{arg}")?;
        }
        write!(w, ")")?;
    }
    Ok(())
}

fn write_arg(w: &mut dyn Write, func: &Function, arg: Value) -> fmt::Result {
    let ty = func.dfg.value_type(arg);
    if let Some(f) = &func.dfg.facts[arg] {
        write!(w, "{arg} ! {f}: {ty}")
    } else {
        write!(w, "{arg}: {ty}")
    }
}

// All of this is just so I can print a function name other than u0:0
pub(crate) fn write_nice_function(
    func_w: &mut NiceFuncWriter,
    w: &mut dyn Write,
    func: &Function,
    name: &str,
) -> fmt::Result {
    write!(w, "function ")?;
    write!(w, "{}{}", name, func.signature)?;
    writeln!(w, " {{")?;
    let aliases = alias_map(func);
    let mut any = func_w.write_preamble(w, func)?;
    for block in &func.layout {
        if any {
            writeln!(w)?;
        }
        decorate_block(func_w, w, func, &aliases, block)?;
        any = true;
    }
    writeln!(w, "}}")
}

/// Re-implementation of `cranelift::codegen::write::alias_map` because it's private
fn alias_map(func: &Function) -> SecondaryMap<Value, Vec<Value>> {
    let mut aliases = SecondaryMap::<_, Vec<_>>::new();
    for v in func.dfg.values() {
        // VADFS returns the immediate target of an alias
        if let Some(k) = func.dfg.value_alias_dest_for_serialization(v) {
            aliases[k].push(v);
        }
    }
    aliases
}

/// Re-implementation of `cranelift::codegen::write::decorate_block` because it's private
fn decorate_block(
    func_w: &mut NiceFuncWriter,
    w: &mut dyn Write,
    func: &Function,
    aliases: &SecondaryMap<Value, Vec<Value>>,
    block: Block,
) -> fmt::Result {
    // Indent all instructions if any srclocs are present.
    let indent = if func.srclocs.is_empty() { 4 } else { 36 };

    func_w.write_block_header(w, func, block, indent)?;
    for a in func.dfg.block_params(block).iter().cloned() {
        write_value_aliases(w, aliases, a, indent)?;
    }

    for inst in func.layout.block_insts(block) {
        func_w.write_instruction(w, func, aliases, inst, indent)?;
    }

    Ok(())
}

/// Re-implementation of `cranelift::codegen::write::write_value_aliases` because it's private
fn write_value_aliases(
    w: &mut dyn Write,
    aliases: &SecondaryMap<Value, Vec<Value>>,
    target: Value,
    indent: usize,
) -> fmt::Result {
    let mut todo_stack = vec![target];
    while let Some(target) = todo_stack.pop() {
        for &a in &aliases[target] {
            writeln!(w, "{1:0$}{2} -> {3}", indent, "", a, target)?;
            todo_stack.push(a);
        }
    }

    Ok(())
}

struct NamedBlockDisplay<'a> {
    block: Block,
    name: Option<&'a Cow<'static, str>>,
}

impl Display for NamedBlockDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name {
            write!(f, "{name}_{}", self.block.as_u32())?;
        } else {
            write!(f, "{}", self.block)?;
        }

        Ok(())
    }
}

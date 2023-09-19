# How to Contribute to Capy

Thank you for investing your time into contributing to Capy! All contributions are welcome. You can try to fix issues, or make issues regarding any bugs you found or possible new features you think may fit :)

## How to make a Pull Request

There are four main points:

- The style guide is "don't make the code look ugly." The default rust formatter is plenty enough.

- Be sure to use `cargo clippy --all-targets`.

- If you're fixing a bug, make sure to include tests for that bug. Most of the crates have good testing capabilities.

- Always review all your changes before you commit.

The last one is especially important. I've found plently of typos / things I've missed by applying it.

But the most important part of contributing is understanding how the codebase works.

## The Structure of Capy's Codebase

As you can probably see pretty easily, Capy consists of several crates, each of which is responsible for an important part of the compilation process.

Actual compilation of source code starts in the `lexer` crate, which converts the code into tokens. Those tokens then get sent to the `parser` crate, which transforms them into an syntax tree.

The `parser` crate works in conjuction with the `ast` (Abstract Syntax Tree) crate, which defines functions for working with the syntax tree.

After that, the tree gets processed by the `hir` (High-level Intermediate Representation) crate. Which handles indexing and lowering of global bodies.

Indexing is essentially just finding out what all the globals are. Global bindings and global functions are discovered here.

Lowering is the process of converting the bodies of globals (which are AST expressions) into HIR expressions. HIR expressions can contain much more relevent information than a syntax tree, and are much easier to work with. Information we don't need is stripped, and the information we *do* need is kept track of neatly. This is in `bodies.rs`.

All those new HIR expressions need to be typed, which is where the `hir_ty` crate comes in. All the crates before this one could've been ran in parallel, but now we have to combine all our work across all our different .capy files into one. This crate not only gives the indexed globals concrete types, but it also does type checking for all expressions everywhere.

Once we've type checked everything, we can finally begin transforming our HIR into machine code with the `codegen` crate. This crate utilizes cranelift to generate actual machine code.

The first thing this crate takes care of is evaluating all `comptime { .. }` blocks by JIT compiling them into functions and then calling those functions. The second thing this crate takes care of is generating the final executable. Under the hood, these two different tasks use the same code for converting HIR into machine instructions.

The central nervous system of the codebase is the `capy` crate, which is essentially a CLI crate. It is kind of complex though if you're trying to wrap your head around how all this fits together. So I'd recommend looking in the `check` function within the `lib.rs` of the `codegen` crate. It contains the most basic code for compiling multiple .capy files.

And that's it! Thank you for spending your time and effort to look into / contribute to this project! It is well appreciated :)

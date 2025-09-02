# How to Contribute to Capy

Thank you for investing your time into contributing to Capy! All contributions are welcome. You can try to fix issues, or make issues regarding any bugs you found or possible new features you think may fit :)

## Where to Start

First, if you want to know what's needed and wanted, you can always look at the [open issues on GitHub](https://github.com/capy-language/capy/issues). Other than these, more tests are *always* appreciated. There are a lot of features and full test coverage has definetly not been acheived yet. This would be the most appreciated in the `hir_ty` and `codegen` crates.

If you want to try and tackle an existing issue, such as fixing a bug or implementing a feature request, all you have to do is comment on that issue saying that you'd like to try and fix / implement it. This way, its clear what everyone is working on and no one steps on each other's toes.

## How to make a Pull Request

There are good resources out there for exactly how to make a Pull Request, but the basic idea is to fork the project, push changes to your fork, and then make a pull request to merge your fork with the main repo.

There are four main points:

- The style guide is "don't make the code look ugly." The default rust formatter is plenty. Make sure to use 4 spaces.

- Be sure to use `cargo clippy --all-targets`.

- If you're fixing a bug, make sure to include tests for that bug. Similarly, include tests for any new features to make sure they work as intended. Most of the crates have good testing capabilities.

- Always review all your changes before you commit.

The last one is especially important. I've found plenty of typos / things I've missed by applying it.

But the most important part of contributing is understanding how the codebase works.

## The Structure of Capy's Codebase

As you can probably see, Capy is a workspace that consists of several crates, each of which is responsible for an important part of the compilation process.

Actual compilation of source code starts in the `lexer` crate, which converts the code into tokens. Those tokens then get sent to the `parser` crate, which transforms them into a syntax tree.

The `parser` crate works in conjuction with the `ast` ([Abstract Syntax Tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree)) crate, which defines functions and structs for working with the syntax tree.

After that, the tree gets processed by the `hir` (High-level Intermediate Representation) crate, which handles indexing and lowering of global variables.

Indexing is just forming a list of each defined global variable. Global bindings are discovered here. This makes the next steps easier. This is done in [`index.rs`](./crates/hir/src/index.rs).

Lowering is the process of converting the values (or bodies) of global variables from AST expressions to HIR expressions. HIR expressions contain much more relevant information than a syntax tree and are much easier to work with. Information we don't need is stripped, and the information we *do* need is kept track of neatly. This is done in [`body.rs`](./crates/hir/src/body.rs).

All those new HIR expressions need to be typed, which is where the `hir_ty` crate comes in. All the crates before this one could've been run in parallel, but now we have to combine all our work across all our different .capy files into one. This crate not only gives the global variables concrete types, but it also does type checking for all expressions everywhere.

Once we've type-checked everything, we can finally begin transforming our HIR into machine code with the `codegen` crate. This crate utilizes [cranelift](https://cranelift.dev/) to generate actual machine code.

The first thing this crate takes care of is evaluating all `comptime { .. }` blocks by JIT compiling them into functions and then calling those functions to get the value. The second thing this crate takes care of is generating the final executable. Under the hood, these two different tasks use the same code for converting HIR into machine instructions (see [`codegen/compiler/functions.rs`](./crates/codegen/src/compiler/functions.rs)).

The central nervous system of the codebase is the `capy` crate, which is essentially a CLI crate. But this crate is kind of complex if you're just trying to learn the basics, so I'd recommend looking at the `check_impl` function within [`codegen/tests.rs`](./crates/codegen/src/lib.rs). It contains the most basic code for compiling multiple .capy files into a binary. Or if you want something even more bare-bones, [`fuzz`](./fuzz/fuzz_targets/main.rs) contains the simplest possible code for transforming source code into typed HIR expressions.

There are a few more helper crates but these aren't too important.

And that's it! Thank you for spending your time and effort to look into and/or contribute to this project! It is well appreciated :)

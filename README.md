<p align=center><img src="./resources/capybara.png" alt="capy icon" height="150"/></p>

# The Capy Programming Language

A statically typed, compiled programming language, largely inspired by Jai, Odin, and Zig.
It even has [arbitrary compile-time execution](#Comptime)!

Now on all your favorite Operating Systems! Thanks [cranelift](https://cranelift.dev/)!

```cpp
core :: mod "core";

to_print :: "Hello, World!";

main :: () -> i32 {
    core.println(to_print);

    // exit with code 0
    0
}
```

*From [`examples/hello_world.capy`](./examples/hello_world.capy)*

## Getting Started

First clone this repo,

```shell
git clone https://github.com/capy-language/capy.git
cd capy
```

Then install the capy command with cargo,

```shell
cargo install --path crates/capy
```

Make sure you have `gcc` installed,

Then compile and run your code!

```shell
capy run examples/hello_world.capy
```

### Basics

Variables are declared with `name : type : value` or `name : type = value`.
The first delcares an immutable binding, and the second declares a mutable variable.

```cpp
name : str : "Terry";

age : i32 = 42;
age = 43;
```

The type can of course be elided.

The binding does not *necessarily* need to be const, it is a runtime store like any other.
But there might be certain circumstances in which it must be, which will be expanded on later.

These bindings and variables can also shadow each other,

```cpp
foo := true;

foo :: 5;

foo := "Hullo :3";
```

Static arrays are declared as follows,

```cpp
my_array := [6] i32 { 4, 8, 15, 16, 23, 42 };

my_array[2] = 10;
```

Slices look very similar but lack the length within the square brackets,

```cpp
my_slice := [] i32 { 1, 2, 3 };

// arrays can be implicitly cast to slices, but casting a slice to an array must be done explicitly

my_new_slice : [] i32 = my_array;
my_new_array : [3] i32 = my_slice as [3] i32;
```

Pointers can be either mutable or immutable, similar to Rust,

```cpp
foo := 5;
bar :: ^mut foo;

bar^ = 10;
```

Unlike Rust however, there are currently no borrow checking rules like "either one mutable reference or many const references".

Mutable pointers greatly improve the readability of code, and allow one to see at a glance the side-effects of a function.

### Types

Types are first-class in Capy, and structs are values which can be assigned to a variable like any other,

```cpp
Person :: struct {
    name: str,
    age: i32
};

gandalf := Person {
    name: "Gandalf",
    age: 2000,
};

// birthday!
gandalf.age = gandalf.age + 1;
```

Types can also be created with the `distinct` keyword, which creates a new type with the same underlying semantics of it's sub type.

```cpp
Imaginary :: distinct i32;

x : Imaginary = 42;
y : i32 = 12;

x = y; // ERROR! Imaginary != i32 :(
```

You can alias a type by making a binding to that type.

```cpp
My_Int :: i32;

x : My_Int = 42;
y : i32 = 12;

x = y; // yay! My_Int == i32 :)
```

It is important to note that in order to use `My_Int` within a type annotation, it must be *const*, or, "known at compile-time."
Otherwise, the compiler will throw an error as it's impossible to compile a variable (`x` in this case) whose type might change at runtime.

```cpp
My_Int := i32;

x : My_Int = 42; // ERROR! My_Int's value might change at runtime! uncompilable!
```

To see all the different types, you can look through [`core/meta.capy`](./core/meta.capy),
which contains reflection related code and documentation for all of Capy's different types.

### Comptime

One of the most powerful parts of the language is its arbitrary compile-time execution.
This allows you to run *any* code at compile-time, returning whatever data you wish.

```cpp
math :: mod "core".math;

powers_of_two := comptime {
    array := [3] i32 { 0, 0, 0 };

    array[0] = math.pow(2, 1);
    array[1] = math.pow(2, 2);
    array[2] = math.pow(2, 3);

    array
};
```

One of the most sacred promises this language tries it's best to keep is *any code that can be run at runtime, can also be run at compile-time*.
There are no `const` functions like in Rust. Mine for crypto, play a video game, or anything else your heart desires within a `comptime` block.
Or at least, that's the end goal. A few things haven't been fully fleshed out yet, like returning types, pointers, and functions from `comptime` blocks.

### Reflection

Reflection is another powerful feature of the language. Currently, you can get all the information you could want concerning types,
including things such as the size of an array type, and the sub-type of a distinct.

```cpp
core :: mod "core";
meta :: core.meta;

ty := [3] i32;
info := meta.get_array_info(ty);

core.assert(info.len == 3);
core.assert(info.ty == i32);
```

This functionality powers the `Any` type, a struct containing an `^any` and a `type`, and which can represent any possible value.

```cpp
count : i32 = 5;
should_start : bool = true;
greeting : str = "Hi";

core.print_any(core.Any {
    ty: i32,
    data: ^count,
});
core.print_any(core.Any {
    ty: bool,
    data: ^should_start,
});
core.print_any(core.Any {
    ty: str,
    data: ^greeting,
});
```

In the future reflection will be made to embrace functions. When user-defined annotations are added, this will result in automation far more powerful than Rust macros.

### Functions

Every Capy program must contain a `main` function. It is the entry point of the program.
This function's signature can be written in multiple ways; it can returning either `void`, or an integer type.

```cpp
// this is valid
main :: () { ... };

// this is also valid
main :: () -> u32 { ... };

/// this isn't :(
main :: () -> bool { ... };
```

In Capy, everything is first-class, and that includes functions.
Functions can be put within variables and bindings just like any other value.

```cpp
add :: (x: i32, y: i32) -> i32 {
    x + y
};

mul :: (x: i32, y: i32) -> i32 {
    x * y
};

apply_2_and_3 :: (func: (x: i32, y: i32) -> i32) -> i32 {
    func(2, 3)
};

apply_2_and_3(add);
apply_2_and_3(mul);
```

Lambdas, or anonymous functions, are a necessity in any good programming language.
This one singular lambda syntax allows for far more consistency and easier code evolution
than the two separate syntaxes for lambdas and functions many languages are forced to go with.

### Imports

Capy contains an `import` and `mod` expression. These are first class values that refer to other files in your program.

An `import` refers to a source file, relative to the current file, whereas a `mod` refers to a specific `mod.capy` file in the global modules directory.

```cpp
my_file :: import "some_file.capy";
core :: mod "core";
```

The modules directory can be changed via the `--mod-dir` flag, and if it lacks a "core" subfolder one will automatically be downloaded from this repository.

The [`examples`](./examples/) folder contains a lot more, and you can read some of them to get a better idea of what the language looks like in practice.

## Limitations

Currently, `gcc` must be installed for the compiler to work.
It is used for linking to libc and producing a proper executable.

If you want to use libc functions, define them with `extern` (look in [`core/libc.capy`](./core/libc.capy) for examples).
Variadic functions do not work. You *could* try explicitly defining a function like `printf` to take 3 arguments,
but this won't work for floats, which are passed into variadic functions differently depending on the calling convention.
Cranelift is [currently working on adding variadic support](https://github.com/bytecodealliance/wasmtime/issues/1030), so that will be added in the future.

While the end goal is to make any code than can run outside of a `comptime` block be allowed to run within a `comptime` block,
this is easier said than done. `printf` in particular cannot be run at compile-time.
And especially as support for linked libaries increases, it'll be harder to keep the promise.

If you find any bugs in the compiler, please please be sure to [make an issue](https://github.com/capy-language/capy/issues) about it and it'll be responded to as soon as possible.

## Shout Outs

Big shout out to [Luna Razzaghipour](https://github.com/lunacookies), the structure of this entire codebase is largely based on [gingerbread](https://github.com/gingerbread-lang/gingerbread) and [eldiro](https://github.com/lunacookies/eldiro).
Her help in teaching how programming languages really work is immeasurable and I'm very thankful.

Big shout out to [cranelift](https://cranelift.dev/). Trying to get LLVM on windows was just way too much effort for me and cranelift made all my dreams come true.

I know the cranelift documentation isn't the greatest, so if anyone wants to use this repo to see how I've implemented higher-level features such as arrays, structs, first class functions, etc. then it's all in [`crates/codegen`](./crates/codegen/).

## License

The Capy Programming Language is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
See [LICENSE-APACHE](./LICENSE-APACHE) and [LICENSE-MIT](./LICENSE-MIT) for details.

The capybara logo was AI generated by [imagine.art](https://www.imagine.art/), who own the rights to it. It can be used in this non-commercial setting with attribution to them.

<p align=center><img src="./resources/capybara.png" alt="capy icon" height="150"/></p>

# The Capy Programming Language

> A programming language made to explore [Compile-Time Execution](#Comptime) and [Runtime Reflection](#Reflection), largely inspired by Jai, Odin, and Zig.

```cpp
core :: mod "core";

greeting :: "Hello, World!";

main :: () -> i32 {
    core.println(greeting);

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
The first is immutable (can't be changed), and the second is mutable (can be changed).

```cpp
name : str : "Terry";

age : i32 = 42;
age = 43; // age can be changed
```

The type can also be omitted.

```cpp
name :: "Terry";
age := 42;
```

Certain other languages have `const` definitions along with immutable variables. Capy combines these two together.
An immutable variable does not *necessarily* need to be known at compile time, it can be a runtime store like any other.
But there might be certain circumstances in which it must be const, which will be expanded on later.

These bindings and variables can also shadow each other,

```cpp
foo := true;

foo :: 5;

foo := "Hullo :3";
```

The value can be omitted and a default/zero value will be supplied.

Fixed arrays are declared as follows,

```cpp
my_array : [6]i32 = i32.[4, 8, 15, 16, 23, 42];

my_array[2] = 10;
```

Slices are a type of pointer that can represent an array of any possible size.
They look very similar but lack a length within the square brackets.

```cpp
my_slice : []i32 = i32.[1, 2, 3];
my_slice : []i32 = i32.[4, 5, 6, 7, 8];

my_slice[2] = 10;
```

Arrays can be implicitly cast to slices, but casting a slice to an array must be done explicitly.

```cpp
// start with an array
my_array : [3]i32 = i32.[2, 4, 8];

// automatically turn it into a slice
my_slice : []i32  = my_array;

// manually turn it back into an array
my_array : [3]i32 = my_slice as [3]i32;
```

Pointers can be either mutable or immutable, similar to Rust.

```cpp
foo := 5;
bar :: ^mut foo;

bar^ = 10;
```

Unlike Rust however, there are currently no borrow checking rules like "either one mutable reference or many const references".

Mutable pointers greatly improve the readability of code, and allow one to see at a glance the side-effects of a function.

### Types

Types are first-class in Capy, which means structs are values that can be assigned to a variable like any other,

```cpp
Person :: struct {
    name: str,
    age: i32
};

gandalf := Person.{
    name = "Gandalf",
    age = 2000,
};

// birthday!
gandalf.age = gandalf.age + 1;
```

Types can also be created with the `distinct` keyword, which creates a new type with the same underlying semantics of it's sub type.

```cpp
Imaginary :: distinct i32;

x : Imaginary = 42;
y : i32 = 12;

y = x; // ERROR! Imaginary != i32 :(
```

You can alias a type by simply assigning it to a variable.

```cpp
My_Int :: i32;

x : My_Int = 42;
y : i32 = 12;

y = x; // yay! My_Int == i32 :)
```

It is important to note that in order to actually use `My_Int` as a type, it must be *const*, or, "known at compile-time."
Otherwise, the compiler will throw an error as it's impossible to compile a variable (`x` in this case) whose type might change at runtime.

```cpp
My_Int := i32;

if random_num() % 2 == 0 {
    My_Int = i64;
}

x : My_Int = 42; // ERROR! My_Int's value might change at runtime! uncompilable!
```

There are two requirements which determine if a variable is *const*.

1. It must be immutable.
2. It must either contain a literal value, a reference to another const variable, or a `comptime` block.

Beyond type annotations, the size of an array is also expected to be *const*, and this value can be calculated using `comptime`.

To see all the different types, you can look through [`core/meta.capy`](./core/src/meta.capy),
which contains reflection related code and documentation for all of Capy's types.

### Comptime

One of the most powerful parts of Capy is its arbitrary compile-time execution.
This allows you to run *any* code at compile-time, returning whatever data you wish.

```cpp
math :: mod "core".math;

powers_of_two := comptime {
    // array with default value (all zeros)
    array : [3]i32;

    array[0] = math.pow(2, 1);
    array[1] = math.pow(2, 2);
    array[2] = math.pow(2, 3);

    array
};
```

One of the most sacred promises Capy tries it's best to keep is *any code that can be run at runtime, can also be run at compile-time*.
There are no special `const` functions to be found here. Mine for crypto, play a video game, or anything else your heart desires within a `comptime` block.
Or at least, that's the end goal. A few wrinkles haven't been fully ironed out yet, like returning pointers and functions from `comptime` blocks.

Types work well with compile-time execution, and can be arbitrarily calculated by whatever code you want,

```cpp
My_Type :: comptime {
    if random_num() % 2 == 0 {
        i32
    } else {
        i64
    }
};

x : My_Type = 42;
```

This obviously isn't the most useful example. Something more pragmatic but far too complex to fit in a readme might be an ORM that automatically downloads the latest schema and uses it to assemble its struct types.

As this feature continues to be fleshed out, this will become the basis of Capy's compile-time generic system.

### Reflection

Reflection is another powerful feature of Capy, and powers the language's [runtime generic system](./core/src/structs/list.capy).

All types in a Capy program become 32 bit IDs at runtime. The [`meta`](./core/src/meta.capy) file of the [`core`](./core) module contains reflection related code for inspecting
these IDs and getting information such as the length of an array type,

```cpp
array_type := [3]i32;
info := meta.get_array_info(array_type);

core.assert(info.len == 3);
core.assert(info.ty  == i32);
```

The size of an integer type,

```cpp
int_type := i16;

core.assert(meta.size_of(int_type)  == 2);
core.assert(meta.align_of(int_type) == 2);
```

The members of a struct,

```cpp
struct_type := struct {
    foo: str
};
info := meta.get_struct_info(struct_type);

first := info.members[0];
core.assert(core.str_eq(first.name,    "foo"));
core.assert(first.ty                == str);
core.assert(first.offset            == 0);
```

And anything else you'd like to know about your types.

This information is supplied in a few global arrays at both runtime and compile-time, meaning that reflection works within both.

This functionality powers the `core.Any` type, which can represent *any* possible value.

```cpp
count        : i32  = 5;
should_start : bool = true;
greeting     : str  = "Hi";

// core.Any contains a type ID and an opaque pointer (like `void*` in C).
// The type ID allows `core.println` to know how to display the given pointer.

core.println(core.Any.{
    ty = i32,
    data = ^count,
});

core.println(core.Any.{
    ty = bool,
    data = ^should_start,
});

core.println(core.Any.{
    ty = str,
    data = ^greeting,
});
```

This is pretty verbose, so the compiler will automatically cast values to a `core.Any` if needed,

```cpp
core.println(5);
core.println(true);
core.println("Hello");
```

This isn't hard coded for the `core.Any` struct, but works for *any* struct with the following members:

```cpp
struct {
    type_id: type,
    opaque_pointer: ^any, // `^any` and `^mut any` are opaque pointers (they have no associated type)
}
```

As you can probably guess, `core.println` internally uses a lot of reflection to determine what to actually print to the screen when given a `core.Any`.
Reflection is extremely useful, and allows for things like a `debug` function that doesn't need to be implemented manually for all types (like Rust), or making it easy to
serialize and deserialize structs.

If `comptime` powers Capy's compile-time generic system, reflection powers Capy's runtime generic system.

In the future reflection will be made to embrace functions. When user-defined annotations are added, this will result in automation far more powerful than Rust macros.

### Defer

The defer statement allows you to code in the future by moving the given expression to the end of the current scope.

The expression in a defer is guarenteed to run, regardless of any breaks or returns.

```cpp
{
    my_file := open_file("foo.txt");
    defer close_file(my_file);

    // do a bunch of stuff with file

} // `close_file` gets run here

```

Defers are "first in, last out". So later defers will run before earlier defers.

```cpp
file_manager := alloc_manager();
defer free_manager(file_manager);

file_manager.foo := open_file("foo.txt");
defer close_file(file_manager.foo);

// foo is freed, and then the file manager is freed
```

### Functions

Every Capy program must contain a `main` function. It is the entry point of the program.
This function's signature can be written in multiple ways; it can return either `void` or an integer type.

```cpp
// this is valid
main :: () { ... };

// this is also valid
main :: () -> u32 { ... };

/// this isn't :(
main :: () -> bool { ... };
```

In Capy, almost everything is first-class, and that includes functions.
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

Lambdas, or anonymous functions, are extremely useful in many programming languages.
This one singular lambda syntax allows for far more consistency and easier code evolution
than the two separate syntaxes for lambdas and functions many languages are forced to go with.

### Imports

Capy contains an `import` and `mod` expression. These are first class values that refer to other files in your program.

An `import` refers to a source file, relative to the current file, whereas a `mod` refers to a specific `mod.capy` file in the global modules directory.

```cpp
my_file :: import "some_file.capy";
core :: mod "core";
```

The modules directory can be changed via the `--mod-dir` flag, and if it lacks a "core" subfolder one will automatically be downloaded [from this repository](./core/).

The [`examples`](./examples/) folder contains a lot more, and it gives a much better idea of what the language looks like in practice.

## Limitations

Currently, `gcc` must be installed for the compiler to work.
It is used for linking to libc and producing a proper executable.

If you want to use libc functions, define them with `extern` (look in [`core/libc.capy`](./core/src/libc.capy) for examples).
Variadic functions do not work. You *could* try explicitly defining a function like `printf` to take 3 arguments,
but this won't work for floats, which are passed into variadic functions differently depending on the calling convention.
Cranelift is [currently working on adding variadic support](https://github.com/bytecodealliance/wasmtime/issues/1030), so that will be added in the future.

While the end goal is to make any code than can run outside of a `comptime` block be allowed to run within a `comptime` block,
this is easier said than done. `printf` in particular cannot be run at compile-time.
Especially as support for linked libaries increases, it'll be harder to keep this promise.

If you find any bugs in the compiler, please be sure to [make an issue](https://github.com/capy-language/capy/issues) about it and it'll be addressed as soon as possible.

## Shout Outs

Big shout out to [Luna Razzaghipour](https://github.com/lunacookies), the structure of this entire codebase is largely based on [gingerbread](https://github.com/gingerbread-lang/gingerbread) and [eldiro](https://github.com/lunacookies/eldiro).
Her help in teaching how programming languages really work is immeasurable and I'm very thankful.

Big shout out to [lenawanel](https://github.com/lenawanel), she's been an enormous help in finding bugs and testing the limits of the language. Due to her help the language has really expanded to new heights.

Big shout out to [cranelift](https://cranelift.dev/). Trying to get LLVM on windows was just way too much effort for me and cranelift made all my dreams come true.

I know the cranelift documentation isn't the greatest, so if anyone wants to use this repo to see how I've implemented higher-level features such as arrays, structs, first class functions, etc. then it's all in [`crates/codegen`](./crates/codegen/).

## Contributing

Capy is open to contributions! See [`CONTRIBUTING.md`](./CONTRIBUTING.md) on how you can contribute. This file also explains how Capy's codebase actually works internally.

## License

The Capy Programming Language is distributed under the terms of both the MIT license and the Apache License (Version 2.0).
See [LICENSE-APACHE](./LICENSE-APACHE) and [LICENSE-MIT](./LICENSE-MIT) for details.

The capybara logo was AI generated by [imagine.art](https://www.imagine.art/), who own the rights to it. It can be used in this non-commercial setting with attribution to them.

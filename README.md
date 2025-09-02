<p align=center><img src="./resources/capybara.png" alt="capy icon" height="150"/></p>

# The Capy Programming Language

> A programming language made to explore [Compile-Time Execution](#Comptime) and [Runtime Reflection](#Reflection), largely inspired by Jai, Odin, and Zig.

```cpp
core :: #mod("core");

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

Make sure you have either `zig` or `gcc` installed (they are used for linking to libc),

Then compile and run your code!

```shell
capy run examples/hello_world.capy
```

### Basics

Variables are declared like this

```cpp
wizard_name: str = "Gandalf";

// alternatively, the compiler can figure out the type for you

wizard_name := "Gandalf";
```

Variables can also be made *immutable* by using `::` instead of `:=`. This prevents them from being updated by other code.

```cpp
age : i32 : 21; // age will stay the same forever!

// like before, you can let the compiler figure out the type for you

age :: 21;
```

Certain other languages have `const` definitions AND immutable variables. Capy combines these two concepts together.
They are both defined the same way, using `::`.

Variables can also shadow each other.
So later definitions will replace earlier definitions that have the same name

```cpp
foo := true;
core.println(foo);  // will print "true"

foo :: 5;
core.println(foo);  // this will print "5"

foo := "Hullo :3";
core.println(foo);  // this will print "Hullo :3"
```

The value of a variable can be omitted and a default/zero value will be supplied.

```cpp
milk : f64;      // without a value, this defaults to 0.0
letter : char;   // without a value, this defaults to '\0'
number : i32;    // without a value, this defaults to 0

// etc. for the other types (excluding pointers and enums)
```

Casting is done with `type.(value)`

```cpp
age_int: i32 = 33;

age_float := f32.(age_int); // casts age_int -> f32

letter := char.(age_int);   // casts age_float -> char
```

Arrays are created like this,

```cpp
the_numbers: [6]i32 = i32.[4, 8, 15, 16, 23, 42];

the_numbers[2] = 10;
```

`[6]i32` is called a *static* array because its size can never be changed later in the code.
However, if you need to store differently sized arrays in the same variable, you can use slices.

Slices are a type of reference that can hold an array of any possible size.
They look very similar but lack a length within the square brackets.

```cpp
the_numbers: []i32 = i32.[4, 8, 15, 16, 23, 42];

the_numbers[2] = 10;

the_numbers = i32.[4, 5, 6, 7, 8];
```

Arrays can automatically cast into slices, which is what's happening above.
If we want to convert a slice back into a fixed array we have to do the cast explicitly,

```cpp
// start with a fixed array
the_numbers: [3]i32 = i32.[2, 4, 8];

// automagically turn it into a slice
my_slice: []i32 = the_numbers;

// manually cast it back to an array
the_numbers: [3]i32 = [3]i32.(my_slice);
```

In Capy, pointers can be mutable or immutable, just like Rust.

```cpp
foo := 5;
bar := ^mut foo;

bar^ = 10;

core.println(foo);  // prints "10"
```

Unlike Rust however, there are currently no borrow checking rules like "either one mutable reference or many const references".
I say *currently* but to be honest I'm not sure if they even should be added down the road.

Mutable pointers greatly improve the readability of code, and allow one to see at a glance the side-effects of a function.

### Types

Types are first-class in Capy. They can be put inside variables, passed to functions, printed, etc.

As an example, structs are usually defined by just assigning a `struct { .. }` value to an immutable variable:

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
gandalf.age += 1;
```

Creating a type alias is as simple as assigning one to an immutable variable

```cpp
My_Int :: i32;

foo : My_Int = 42;
bar : i32 = 12;

bar = foo;
```

It is important to note that in order to actually use a variable as a type, it must be *const*, or, "known at compile-time."
Otherwise, the compiler will throw an error as it's impossible to compile a variable whose type might change at runtime,

```cpp
// notice how this variable is mutable `:=`
My_Int := i32;

if random_num() % 2 == 0 {
    My_Int = i64;
}

x : My_Int = 42; // ERROR! My_Int's value might change at runtime! uncompilable!
```

There are two requirements which determine if a variable is *const*.

1. It must be immutable.
2. It must either contain a literal value, a reference to another const variable, or a `comptime` block.

Beyond just being used for types, Const variables can also be used for enum discriminants (explained later) and array sizes.

#### Distinct types

New types can also be created with the `distinct` keyword, which creates a new type with the same underlying semantics of its sub type

```cpp
Seconds :: distinct i32;

foo : Seconds = 42;
bar : i32 = 12;

bar = foo; // ERROR! Seconds != i32
```

This can be useful for making sure one doesn't mix up `Seconds` for `Minutes` for e.g.

#### Enums

Enums are an incredibly useful construct for dealing with varying state.
In Capy enums look like this:

```cpp
Dessert :: enum {
    Ice_Cream,
    Chocolate_Cake,
    Apple_Pie,
    Milkshake,
};

order_list := Dessert.[
    Dessert.Chocolate_Cake,
    Dessert.Ice_Cream,
    Dessert.Milkshake,
];
```

Enums can also have additional data associated with each variant, and this data can be extracted using `switch` statements

```cpp
Web_Event :: enum {
    Page_Load,
    Page_Unload,
    Key_Press: char,
    Paste: str,
    Click: struct {
        x: i64,
        y: i64,
    },
};

pressed : Web_Event = Web_Event.Key_Press.('x');
pasted : Web_Event = Web_Event.Paste.("hi hi hi :)");
clicked : Web_Event = Web_Event.Click.{
    x = 20,
    y = 80
};

switch e in clicked {
    .Page_Load => core.println("page loaded"),
    .Page_Unload => core.println("page unloaded"),
    .Key_Press => {
        // type_of(e) == char
        core.println("pressed key: ", e);
    },
    .Paste => {
        // type_of(e) == str
        core.println("pasted: ", e);
    },
    .Click => {
        // type_of(e) == struct { x: i64, y: i64 }
        core.println("clicked at x=", e.x, ", y=", e.y);
    }
}
```

As you can see, switches declare an *argument* (`e`, in this case), and the type of that argument changes depending on the branch.

One of the unique things about Capy's enums is that each variant of the enum is actually its own unique type.
When you define the variants `Web_Event.Click`, `Web_Event.Paste`, `Dessert.Chocolate_Cake`, etc. inside an `enum {}` block
you are actually creating entirely new types. You can reference and instantiate these types just like any other type.

```cpp
special_click_related_code :: (click_event: Web_Event.Click) {
    core.println(click_event.x);
}
```

It's very similar to creating distincts. The only real difference is that enums allow you to mix the different variants together.

Being able to operate on each variant as its own type can be quite useful, and doing things like this in Rust can be verbose.

<details> 
<summary>Extra enum information</summary>

If you're doing FFI and you need to specify the discriminant you can do that with `|`

```cpp
Error :: enum {
    IO: str     | 10,
    Caught_Fire | 20,
    Exploded    | 30,
    Buggy_Code  | 40,
}
```

In memory, the discriminant is always a u8 that comes after the payload of the enum itself.
Reflection can be used to see what the byte offset of the discriminant is. [`core/meta.capy`](./core/src/meta.capy)

*[`examples/enums_and_switch_statements.capy`](./examples/enums_and_switch_statements.capy) contains more examples*

</details>

#### Optionals & Error handling

Error handling can really make or break a language.

A programming language's error handling system will be used constantly, whether it's exceptions, errors as values, aborting, or whatever else.
Making sure it's expressive and easy to use is very important.

In Capy's case, the error handling system is heavily inspired by Zig's, with a few key differences.

An optional type can be declared by using `?`

```cpp
message : ?str = nil;

message = "hello";
```

Optionals represent the presence or absence of a value.

Capy does not have null pointers.
They've been called a "billion dollar mistake" and from my own personal experience they're such a pain to deal with.
All pointer types, `^i32`, `^bool`, etc. are forbidden from ever being null.

Instead, nullable pointers must be *explicitly* declared by using optional types

```cpp
foo : i32 = 42;

// This is a regular pointer.
// You can use this freely in your program and dereference it at will
regular_ptr : ^i32 = ^foo;

// This is a nullable pointer.
// You must explicitly check it before dereferencing it
nullable_ptr : ?^i32 = ^foo;

// this is what it looks like to make `nullable_ptr` null
nullable_ptr = nil;
```

Of course, sometimes it's not enough to just know that a value isn't there.
Sometimes you need to know *why* the value isn't there.

Capy doesn't use exceptions. Errors are values just like any other value in your program.

An *error union* type can be used to return either a successful value or an error.
Error unions are created with `<error type>!<success type>`.

For example:

```cpp
do_work :: (task_number: i32) -> str!f32 {
    // ...
}
```

This function `do_work` will try to return an `f32`, but if there was some kind of error it will return `str` instead.

This is very similar to Zig's method of error handling although the problem with Zig's system is that they heavily restrict
what kind of errors you can return. Imagine parsing a 12KB json file and just getting `InvalidCharacter`.

In Capy the errors can be whatever you want.

```cpp
My_Custom_Error :: enum {
    ID_Too_Big,
    Bad_ID: struct {
        why: str,
    },
    Caught_Fire,
};

try_to_double :: (id: u64) -> My_Custom_Error!u64 {
    if id == 5 {
        return My_Custom_Error.Bad_ID.{ why = "I don't like it" };
    }

    if id > 10 {
        return My_Custom_Error.ID_Too_Big;
    }

    id * 2
}
```

Enums, optionals, and error unions, are all called *sum types* because they're "true" type might vary between between one of several at runtime.

Enums can be any one of their variants.
Optionals can be either the success type, or the type `nil`.
Error Unions can be either the success type, or the error type.

Switches work for all sum types where each arm of the switch statement is a possible "true" type

```cpp
// switching on an optional

message : ?str = "Hello, World!"

switch inner in message {
    str => {
        // type_of(inner) == str
        core.println("The message is: ", inner);
    }
    nil => {
        // type_of(inner) == nil
        // "nil" is its own type
        core.println("There is no message :(");
    }
}

// switching on an error union

switch inner in try_to_double(5) {
    u64 => {
        // type_of(inner) == u64
        core.println("successfully doubled!\nthe result is = ", inner);
    }
    My_Custom_Error => {
        // type_of(inner) == My_Custom_Error
        core.println("Uh oh, there was an error: ", inner);
    }
}
```

You can also use the compiler directives `#is_variant` and `#unwrap` to quickly assert that a sum type has a particular "true" type

```cpp
message : ?str = nil;

if #is_variant(message, str) {
    val := #unwrap(message, str);
}


result := try_to_double(11);

if #is_variant(result, u64) {
    doubled := #unwrap(result, u64);
}

// these also work for enums
```

Note: if the first argument is an optional, both `#unwrap(message, str)` and `#unwrap(message)` are equivalent

The one place where optionals and error unions differ from enums is that optionals and error unions allow you to use the `.try` keyword.

`.try` is an operator which will return an error/nil value if it finds one, and otherwise will continue execution like normal.
For example:

```cpp
do_networking :: () -> My_Error_Type!u32 {
    body := get_request("https://example.com").try;

    version_number := parse_number(body).try;

    save_number_to_disk(version_number).try;

    200
}

get_request :: (url: str) -> My_Error_Type!str {}
parse_number :: (text: str) -> My_Error_Type!u64 {}
save_number_to_disk :: (number: u64) -> My_Error_Type!void {}
```

The above code is equivalent to this:

```cpp
do_networking :: () -> My_Error_Type!u32 {
    body := switch inner in get_request("https://example.com") {
        str => inner,
        My_Error_Type => {
            return inner;  
        },
    };

    version_number := switch inner in parse_number(body) {
        u64 => inner,
        My_Error_Type => {
            return inner;
        },
    };

    switch inner in save_number_to_disk(version_number) {
        void => {},
        My_Error_Type => {
            return inner;
        }
    }

    200
}

get_request :: (url: str) -> My_Error_Type!str {}
parse_number :: (text: str) -> My_Error_Type!u64 {}
save_number_to_disk :: (number: u64) -> My_Error_Type!void {}
```

This is an example using error unions, but `.try` works for optionals as well. If the inner value is `nil`, it will return early.

#### Summary

With that, here are all the possible types data can have in Capy:

1. Signed integers          (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`)
2. Unsigned integers        (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`)
3. Floating-point numbers   (`f32`, `f64`)
4. `bool`
5. `str`
6. `char`
7. Fixed arrays (`[6]i32`, `[3]f32`, `[10]bool`, etc.)
8. Slices       (`[]i32`, `[]f32`, `[]bool`, etc.)
9. Pointers     (`^i32`, `^f32`, `^mut bool`, etc.)
10. Distincts   (`distinct i32`, `distinct f32`, `distinct bool`, etc.)
11. Structs     (`struct { a: i32, b: i32 }`, `struct { foo: str }`, etc.)
12. Enums       (`enum { Foo: i32, Bar: str, Baz: bool }`, etc.)
13. Variants    (each variant of an enum is a unique type, like distincts)
14. Functions   (`() -> void`, `(x: i32) -> bool`, etc.)
15. Files       (when you import a file, that file is actually its own type)
16. `type`      (types are first-class and `i32` when used as a value has the type `type`)
17. `any`       (a reference type, explained later)
18. `rawptr`, `mut rawptr`  (opaque pointers, like void* in C)
19. `rawslice`              (an opaque slice)
20. `void`

You can also look through [`core/meta.capy`](./core/src/meta.capy),
which contains [reflection](#Reflection) related code and documentation for all of Capy's types.

### Comptime

One of the most powerful features of Capy is its arbitrary compile-time execution.
This allows you to run *any* code at compile-time, returning whatever data you wish.

```cpp
math :: #mod("core").math;

powers_of_two := comptime {
    // array with default value (all zeros)
    array : [3]i32;

    array[0] = math.pow_i32(2, 1);
    array[1] = math.pow_i32(2, 2);
    array[2] = math.pow_i32(2, 3);

    array
};
```

One of the most sacred promises Capy tries its best to keep is *any code that can be run at runtime, can also be run at compile-time*.
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

Something more pragmatic but far too complex to fit in a readme might be an ORM that automatically downloads the latest schema and uses it to assemble its struct types.

As this feature continues to be fleshed out, this will become the basis of Capy's compile-time generic system.

### Reflection

Reflection is another powerful feature of Capy, and powers the language's [runtime generic system](./core/src/structs/list.capy).

All types in a Capy program become 32 bit IDs at runtime. The [`meta`](./core/src/meta.capy) file of the [`core`](./core) module contains reflection related code for inspecting these IDs and getting information such as the length of an array type,

```cpp
array_type := [3]i32;

switch info in meta.get_type_info(array_type) {
    .Array => {
        core.assert(info.len    == 3);
        core.assert(info.sub_ty == i32);
    }
    _ => {}
}
```

The size of an integer type,

```cpp
int_type := i16;

switch info in meta.get_type_info(int_type) {
    .Int => {
        core.assert(info.bit_width == 16);
        core.assert(info.signed    == true);
    }
    _ => {}
}
```

The members of a struct,

```cpp
struct_type := struct {
    foo: str
};

switch info in meta.get_type_info(struct_type) {
    .Struct => {
        first := info.members[0];
        core.assert(first.name   == "foo"));
        core.assert(first.ty     == str);
        core.assert(first.offset == 0);
    }
    _ => {}
}
```

And anything else you'd like to know about your types.

This information is supplied in a few global arrays at both runtime and compile-time, meaning that reflection works within both.

This functionality powers the `any` type, which can represent *any* possible value.

```cpp
count        : any = 5;
should_start : any = true;
greeting     : any = "Hi";

core.println(count);
core.println(should_start);
core.println(greeting);
```

`any` is a reference type, and internally contains a type ID and a rawptr. Using reflection on the type ID is what allows functions like `core.println` to know what to do with the given pointer.

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

// foo is closed, and *then* the file manager is freed
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

### Compiler Directives

Capy uses compiler directives to do special operations that couldn't be achieved with regular functions.

`#import` and `#mod` are used to refer to other files in your program. Just like types, They are first-class values.
`#import` refers to a source file, relative to the current file, whereas `#mod` refers to a specific module in the global modules directory.

```cpp
my_file :: #import("some_file.capy");
core    :: #mod("core");
```

The modules directory can be changed via the `--mod-dir` flag, and if it lacks a "core" subfolder one will automatically be downloaded [from this repository](./core/).

`#unwrap` asserts that an enum is a certain variant, and panics otherwise.

```cpp
some_event : Web_Event = Web_Event.Click.{
    x = 20,
    y = 80
};

clicked : Web_Event.Click = #unwrap(some_event, Web_Event.Click); 
```

The [`examples`](./examples/) folder contains a lot more, and it gives a much better idea of what the language looks like in practice.

## Limitations

Currently, either `zig` or `gcc` must be installed for the compiler to work.
They are used for linking to libc and producing a proper executable.

If you want to use libc functions, define them with `extern` (look in [`core/libc.capy`](./core/src/libc.capy) for examples).
Variadic extern functions do not work. You *could* try explicitly defining a function like `printf` to take 3 arguments,
but this won't work for floats, which are passed into variadic functions differently depending on the calling convention.
Cranelift is [currently working on adding variadic support](https://github.com/bytecodealliance/wasmtime/issues/1030), so that will be added in the future.

While the end goal is to make any code than can run outside of a `comptime` block be allowed to run within a `comptime` block,
this is easier said than done. `printf` in particular cannot be run at compile-time. Although things like this are being worked on.

If you find any bugs in the compiler, please be sure to [make an issue](https://github.com/capy-language/capy/issues) about it and it'll be addressed as soon as possible.

## Shout Outs

Big shout out to [Luna Razzaghipour](https://github.com/lunacookies), the structure of this entire codebase is largely based on [gingerbread](https://github.com/gingerbread-lang/gingerbread) and [eldiro](https://github.com/lunacookies/eldiro).
Her help in teaching how programming languages really work is immeasurable and I'm very thankful.

Big shout out to [lenawanel](https://github.com/lenawanel), she's been an enormous help in testing the limits of the language and improving the compiler in so many ways. Due to her help the language has gotten much more complete than I would've been able to accomplish myself.

Big shout out to [cranelift](https://cranelift.dev/). Trying to get LLVM on windows was just way too much effort for me and cranelift made all my dreams come true.

I know the cranelift documentation isn't the greatest, so if anyone wants to use this repo to see how I've implemented higher-level features such as arrays, structs, first class functions, etc. then it's all in [`crates/codegen`](./crates/codegen/).

This project was made by [NotAFlyingGoose](https://github.com/NotAFlyingGoose) :)

## Contributing

Capy is open to contributions! See [`CONTRIBUTING.md`](./CONTRIBUTING.md) on how you can contribute.

Even if you're not at all interested in contributing, this file explains how Capy's codebase works, which might be a good read if you're interested in compilers.

## License

The Capy Programming Language is licensed under the Apache License (Version 2.0) with Runtime Library Exception or the MIT license, at your option.
See [LICENSE-APACHE](./LICENSE-APACHE) and [LICENSE-MIT](./LICENSE-MIT) for details.

It is Copyright (c) The Capy Programming Language Contributors.

The Runtime Library Exception makes it clear that end users of the Capy compiler don’t have to attribute their use of Capy in their finished binary application, game, or service. End-users of the Capy Programming Language should feel unrestricted to create great software. The full text of this exception follows:

```
As an exception, if you use this Software to compile your source code and
portions of this Software are embedded into the binary product as a result,
you may redistribute such product without providing attribution as would
otherwise be required by Sections 4(a), 4(b) and 4(d) of the License.
```

This exception can be found at the bottom of the [LICENSE-APACHE](./LICENSE-APACHE) file.
This is the same exception used by the [Swift programming language](https://www.swift.org/legal/license.html).

The capybara logo was AI generated by [imagine.art](https://www.imagine.art/), who own the rights to it. It can be used in this non-commercial setting with attribution to them.

I would honestly rather pay an artist to make a proper logo, but I wouldn't know how to do that.

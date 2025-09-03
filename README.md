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

Variables are declared with `name : type = value`

```cpp
wizard_name: str = "Gandalf";

// if you leave out the type, the compiler will figure it out for you

wizard_name := "Gandalf";
```

Variables can be made *immutable* by using `::` instead of `:=`.
This prevents other code from changing the variable in any way.

```cpp
age : i32 : 21;

age = 22; // ERROR! age is immutable

// just like before, the compiler will figure out the type if you leave it out

age :: 21;
```

Certain other languages have `const` definitions AND immutable variables.
Capy combines these two concepts together. They are both defined with `::`.

Capy's definition of what *const* means will be explained later.

Variables can shadow each other.
This means that later definitions will replace earlier definitions with the same name.

```cpp
foo := true;
core.println(foo);  // prints "true"

foo :: 5;
core.println(foo);  // now prints "5"

foo := "Hullo :3";
core.println(foo);  // now prints "Hullo :3"
```

The value of a variable can be omitted and a default/zero value will be supplied.

```cpp
milk : f64;      // without a value, this defaults to 0.0
letter : char;   // without a value, this defaults to '\0'
number : i32;    // without a value, this defaults to 0

// etc. for the other types (excluding pointers, slices, enums, and error unions)
```

Casting is done with `type.(value)`

```cpp
age_int: i32 = 33;

age_float := f32.(age_int); // casts i32 -> f32

letter := char.(age_int);   // casts f32 -> char
```

Arrays can be created with `type.[value1, value2, value3, ...]`

```cpp
the_numbers: [6]i32 = i32.[4, 8, 15, 16, 23, 42];

the_numbers[2] = 10;
```

The type of this above array is `[6]i32`.
`[6]i32` is called a *static* array because its size can never change.

If you won't know the size of the array until runtime, *slices* can be used instead.

Slices can reference any array, no matter the size. To get a *slice* of `i32`s, you'd write `[]i32` 

```cpp
list_one: [6]i32 = i32.[4, 8, 15, 16, 23, 42];
list_two: [3]i32 = i32.[2, 4, 8];

my_slice: []i32 = list_one;

// my_slice can be reassigned to reference an array of some other size
my_slice        = list_two;
```

As seen above, static arrays will automatically fit themselves into slice types if the underlying type
(in this case, `i32`) matches.

If you want to get the underlying static array of a slice, you must manually cast it.

```cpp
list_one: [3]i32 = i32.[2, 4, 8];

my_slice: []i32 = list_one; // this is automatic

list_two: [3]i32 = [3]i32.(my_slice); // this is a manual cast of []i32 -> [3]i32
```

Pointers are created with `^value` or `^mut value`

In Capy, pointers are either mutable or immutable, like Rust.

```cpp
foo := 5;
bar := ^mut foo;

bar^ = 10;

core.println(foo);  // prints "10"
```

Unlike Rust however, there are currently no borrow checking rules like "either one mutable reference or multiple immutable references".

I say *currently* but to be honest I'm not sure if they even should be added down the road.

Mutable pointers greatly improve the readability of code, and allow one to see at a glance the side-effects of a function.

### Types

Types are first-class in Capy. They can be put inside variables, passed to functions, printed, etc.

As an example, structs are usually defined by creating a new immutable variable and assigning a `struct { .. }` value to it.

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

The `struct { .. }` value above represents the type definition itself.

Any type can be assigned to any variable.

This system means that type aliasing is dead simple.

```cpp
My_Int :: i32;

foo : My_Int = 42;
bar : i32 = 12;

bar = foo; // This works because My_Int == i32
```

Immutable variables like `Person`, `My_Int`, etc., can be used in place of a type annotation (as seen above).

It's important to note that there are certain rules about when a variable can be used as a type.
It largely depends on whether the variable is *const*, or, "known at compile-time."

If a variable isn't const, the compiler will produce an error because
it's impossible to compile a variable whose type might change at runtime.

```cpp
My_Int := i32; // notice how this variable is mutable `:=`

if random_num() % 2 == 0 {
    My_Int = i64;
}

x : My_Int = 42; // ERROR! My_Int's value might change at runtime! uncompilable!
```

There are two requirements which determine if a variable is *const*.

1. It must be immutable (it must use `::` and not `:=`)
2. It must contain a literal value, a reference to another const variable, or a `comptime` block.

Beyond just being used for types, Const variables can also be used for enum discriminants (explained later) and array sizes.

#### Distinct types

Types can be created with the `distinct` keyword, which creates a new type that has the same underlying semantics of its sub type

```cpp
Seconds :: distinct i32;

foo : Seconds = 42;
bar : i32 = 12;

bar = foo; // ERROR! Seconds != i32
```

This can be useful for making sure one doesn't mix up `Seconds` for `Minutes` for e.g.

#### Enums

Enums are incredibly useful for dealing with varying state.
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

Enums can have additional data associated with each variant, and this data can be extracted using `switch` statements

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

event_queue : []Web_Event = .[
    Web_Event.Page_Load,
    Web_Event.Key_Press.('x'),
    Web_Event.Paste.("hi hi hi :)"),
    Web_Event.Click.{
        x = 20,
        y = 80
    }
];

switch e in event_queue[0] {
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
you are actually creating entirely new distinct types. You can reference and instantiate these types just like any other type.

```cpp
special_click_related_code :: (click_event: Web_Event.Click) {
    core.println(click_event.x);
}
```

It's very similar to creating distincts. The only real difference is that enums allow you to mix the different variants together.

Being able to operate on each variant as its own type can be quite useful, and doing things like this in Rust can be verbose.

<details> 
<summary>Extra Information About Enums</summary>

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

---

</details>

#### Optionals & Error handling

Error handling can really make or break a language.

A programming language's error handling system will be used constantly, whether it's exceptions, errors as values, aborting, or whatever else.
Making sure it's expressive and easy to use is very important.

In Capy's case, the chosen error handling system is heavily inspired by Zig's, with a few key differences.

An optional type can be declared with `?type`

```cpp
message : ?str = nil;

message = "hello";
```

Optionals represent the presence or absence of a value, which might change at runtime.

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

// `nil` acts like a null pointer here
nullable_ptr = nil;
```

Of course, sometimes it's not enough just to know that a value isn't there.
Sometimes you need to know *why* the value isn't there.

An *Error Union* type can be used to represent either a successful value or an error.

Error unions are created with `<error type>!<success type>`.

For example:

```cpp
do_work :: (task_number: i32) -> str!f32 {
    // ...
}
```

What `str!f32` means is that this function, `do_work`, will normally return an `f32`,
but if `do_work` runs into some kind of problem that prevents it from functioning properly,
a value of type `str` will be returned instead.

This is very similar to Zig's method of error handling, although the problem with Zig's system is that it heavily restricts
what kind of errors you can return. Imagine parsing a 12KB json file and just getting `InvalidCharacter`.

The above example had a `str` error type, but in Capy the errors can really be whatever you want.

```cpp
Custom_Error :: enum {
    Input_Too_Big,
    Bad_Input: struct {
        why: str,
    },
    Caught_Fire,
};

try_to_double :: (num: u64) -> Custom_Error!u64 {
    if num == 5 {
        return Custom_Error.Bad_Input.{ why = "I don't like it" };
    }

    if num > 10 {
        return Custom_Error.Input_Too_Big;
    }

    num * 2
}
```

Enums, optionals, and error unions, are all called *sum types* in Capy because they represent
data whose "true" type will vary between one of several at runtime.

The "true" type of an enum can be any one of the variants at runtime.

The "true" type of an optional can be either the success type or the type `nil` at runtime.

The "true" type of an error union can be either the success type or the error type at runtime.

Switches aren't just for enums, they can be used with any sum type.
Each arm of the switch statement represents one of the possible "true" types of the given data.

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
        // note: `nil` is a type, just like `i32` or `void`
        // the `nil` keyword represents both the type `nil`
        // and the value `nil`
        core.println("There is no message :(");
    }
}

// switching on an error union

switch inner in try_to_double(5) {
    u64 => {
        // type_of(inner) == u64
        core.println("successfully doubled!");
        core.println("the result is = ", inner);
    }
    Custom_Error => {
        // type_of(inner) == Custom_Error
        core.println("Uh oh, there was an error: ", inner);
    }
}
```

You can also use the compiler directives `#is_variant` and `#unwrap` to quickly assert the "true" type of a given sum type

```cpp
// With an optional

message : ?str = nil;

if #is_variant(message, str) {
    val := #unwrap(message, str);
}

// With an error union

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

The above example uses `.try` with error unions, but `.try` works for optionals as well.

<details> 
<summary>Extra Information About Optionals & Error Unions</summary>

Optionals and Error Unions are stored in memory as tagged unions, just like enums.

The "success" discriminant is 1, and the "error" (or "nil") discriminant is 0

Regular pointers are considered "non-zero" in Capy,
and the size of a non-zero type is equal to the size of its optional.

This means that e.g. `size_of(?^i32) == size_of(^i32)` but `size_of(?i32) != size_of(i32)`

Since the inner type can never be zero, an inner value of zero is used to represent the "nil" state.
This allows non-zero optionals to have zero memory cost.

---

</details>

#### Type Summary

With that, here are all the possible types in Capy:

1. Signed integers          (`i8`, `i16`, `i32`, `i64`, `i128`, `isize`)
2. Unsigned integers        (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`)
3. Floating-point numbers   (`f32`, `f64`)
4. `bool`
5. `str`
6. `char`
7. Static arrays            (`[6]i32`, `[3]f32`, `[10]bool`, etc.)
8. Slices                   (`[]i32`, `[]f32`, `[]bool`, etc.)
9. Pointers                 (`^i32`, `^f32`, `^mut bool`, etc.)
10. Distincts               (`distinct i32`, `distinct f32`, `distinct bool`, etc.)
11. Structs                 (`struct { a: i32, b: i32 }`, `struct { foo: str }`, etc.)
12. Enums                   (`enum { Foo: i32, Bar: str, Baz: bool }`, etc.)
13. Enum variants           (each variant of an enum is treated as a special kind of distinct type)
14. Functions               (`() -> void`, `(x: i32) -> bool`, etc.)
15. Files                   (when you import a file, that file is actually its own type, like a struct)
16. `type`                  (types are first-class and "`i32`" when used as a value has the type `type`)
17. `any`                   (a reference type, explained later)
18. `rawptr`, `mut rawptr`  (opaque pointers, like void* in C)
19. `rawslice`              (an opaque slice)
20. `void`

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

One of the most sacred and holy promises Capy tries to keep is:
*"any code which can run at runtime, shall also be runnable at compile-time"*.

There are no special `const` functions to be found here.

Mine for crypto, play a video game, or anything else your heart desires within a `comptime` block.
Or at least, that's the end goal. A few wrinkles haven't been fully ironed out yet, like returning pointers and functions from `comptime` blocks.

Compile-time execution is very useful, and can even be used to do things like arbitrarily calculating a particular type

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

Something more pragmatic than the above (but far too complex to fit in a readme) might be an ORM that automatically downloads the latest schema and uses it to assemble struct types.

As this feature continues to be fleshed out, this will become the basis of Capy's compile-time generic system.

Additionally, at some point I'd like to make it so code within the comptime block can directly interface with the compiler, like a build.zig file, but within a `comptime { .. }` block.

### Reflection

Reflection is another powerful feature of Capy, and powers the language's [runtime generic system](./core/src/structs/list.capy).

All types in a Capy program become 32 bit IDs at runtime. The [`meta.capy`](./core/src/meta.capy) file of the [`core`](./core) module contains reflection related code for inspecting these IDs and getting information such as the length of an array type,

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

This information is supplied in a few global arrays at both runtime and compile-time, meaning that reflection works in both.

This functionality powers the `any` type, which can represent *any* possible value.

```cpp
count        : any = 5;
should_start : any = true;
greeting     : any = "Hi";

core.println(count);
core.println(should_start);
core.println(greeting);
```

`any` is a reference type, and internally contains a type ID and a rawptr.
Functions like `core.println` use reflection on this type ID to determine how to print the given rawptr.

Reflection is extremely useful, and allows for things like a `debug` or `serialize` function that doesn't need to be implemented manually for all types (like Rust).

If `comptime` powers Capy's compile-time generic system, reflection powers Capy's [runtime generic system](./core/src/structs/list.capy).

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

// the foo file is closed, and *then* the file manager is freed
```

Speaking of breaks and returns, there's no better place to talk about them than right here

In Capy, `break` acts like a `goto` in C, jumping to the last labeled block, if statement, or loop

```cpp
{
    // doing stuff...

    `my_block_label: {
        // imagine code here...

        if true {
            // inside an if statement...

            {

                break;

            }
        }

    } // <- the `break` will jump to the end of this block
}
```

`break` can also be used with a value to easily return something from a block expression.

```cpp
foo := `foo_calc: {
    if 2 < 5 {
        break `foo_calc 42;
    }

    5
};
```

`return` works similarly to a `break`, except that instead of jumping to the last labeled scope,
it jumps to the *very first scope* regardless of if its a function or not.


```cpp
global_variable_1 :: true;

global_variable_2 :: comptime {
    if global_variable_2 {
        return 42;
    }

    5
};
```

There's not much to say about `continue`. It works exactly like you'd expect it to.

### Functions

Lambdas, or anonymous functions, are extremely useful in all the programming languages that have them.

Capy has only one way of creating functions:

```
(param1: type1, param2: type2, ...) -> return_type { <code here> }
```

These function values can be passed around and given to other functions, they can be assigned to variables, etc.

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
apply_2_and_3((x: i32, y: i32) -> i32 {
    (10*x + 10*y) / 2
});
```

This singular, combined syntax for lambdas and named functions allows for far more consistency and easier code evolution
than the two separate syntaxes many languages are forced to go with.

Every Capy program must contain a `main` function. It is the entry point of the program.
This function's signature can be written in multiple ways; it can return either `void` or an integer type.

```cpp
// this is valid
main :: () { ... };

// this is also valid
main :: () -> u32 { ... };

/// this isn't
main :: () -> bool { ... };
```

### Compiler Directives

Capy uses compiler directives to do special operations that couldn't be achieved with code.

`#import` and `#mod` are used to refer to other files in your program. Just like types, They are first-class values.
`#import` refers to a source file, relative to the current file, whereas `#mod` refers to a specific module in the global modules directory.

```cpp
my_file :: #import("some_file.capy");
core    :: #mod("core");
```

The modules directory can be changed via the `--mod-dir` compiler flag, and if it lacks a "core" subdirectory one will automatically be downloaded [from this repository](./core/).

Another directive is `#unwrap`, which asserts that an enum is a certain variant, and panics otherwise.

```cpp
some_event : Web_Event = Web_Event.Click.{
    x = 20,
    y = 80
};

clicked : Web_Event.Click = #unwrap(some_event, Web_Event.Click); 
```

`#unwrap` requires the first argument to be a sum type value, and the second argument to be the expected "true" type.
The second argument is not required if the first argument is an optional.

`#is_variant` returns `true` if a sum type is the specified "true" type

The first argument must be a sum type value, and the second argument must be the expected "true" type.
Unlike `#unwrap`, the second argument is always required.

### Operators

Binary Operators:

| Name                | Symbols              | Types                                              |
| ------------------- | -------------------- | -------------------------------------------------- |
| Arithmetic          | `+`, `-`, `*`, `/`   | integers,<br>floats                                |
| Modulo              | `%`                  | integers                                           |
| Exclusive OR        | `~`                  | integers,<br>floats                                |
| Bit Shift           | `<<`, `>>`           | integers                                           |
| Binary AND/OR       | `&`, `\|`            | integers,<br>floats,<br>booleans                   |
| Logical AND/OR      | `&&`, `\|\|`         | booleans                                           |
| Order Comparison    | `<`, `>`, `<=`, `>=` | integers,<br>floats,<br>booleans                   |
| Equality Comparison | `==`, `!=`           | (all types other than pointers, slices, and `any`) |

Prefix Operators:

| Name                      | Symbols    | Types               | Example         |
| ------------------------- | ---------- | ------------------- | --------------- |
| Negation and Positivity   | `-`, `+`   | integers,<br>floats |                 |
| Binary NOT                | `~`        | integers,<br>floats |                 |
| Logical NOT               | `!`        | booleans            |                 |
| Array Type Declaration    | `[]`       | works for any type  | `[size]type`    |
| Optional Type Declaration | `?`        | works for any type  | `?type`         |
| Pointer Type Declaration  | `^`        | works for any type  | `^type`         |
| Distinct Type Declaration | `distinct` | works for any type  | `distinct type` |

Postfix Operators:

| Name                 | Symbols | Types                      | Example                      |
| -------------------- | ------- | -------------------------- | ---------------------------- |
| Array Index          | `[]`    | arrays,<br>slices          | `array[index]`               |
| Function Call        | `()`    | functions                  | `function(arg1, arg2, ...)`  |
| Dereference          | `^`     | pointers                   | `pointer^`                   |
| Propagation          | `.try`  | error unions,<br>optionals | `error_union.try`            |
| Cast                 | `.()`   | works for any type         | `type.(value)`               |
| Array Instantiation  | `.[]`   | works for any type         | `type.[value1, value2, ...]` |
| Struct Instantiation | `.{}`   | works for any struct type  | `type.{ field = value }`     |

All operators that work for one type will also work for a distinct of that type.

Note that array/struct instantiation can be done without an explicit type.
This creates an *anonymous* array or struct

```cpp
bob := .{
    name = "Bob",
    age = 20,
};

things := .[1, 2, 3];
```

anonymous arrays and structs will automatically convert to any strongly typed array or struct they encounter.

The [`examples`](./examples/) directory contains a lot more than has been gone over in this section detailing the language,
and it gives a much better idea of what the language looks like in practice.

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

Big shout out to [lenawanel](https://github.com/lenawanel), she's been an enormous help in testing the limits of the language and improving the compiler in so many ways. Due to her help the language has become much more complete than I would've been able to accomplish myself.

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

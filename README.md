# The Capy Programming Language

A cool programming language, largely inspired by Jai, Odin, and Zig. Compile-time evaluation coming soon.

Now on all your favorite Operating Systems! Thanks [cranelift](https://cranelift.dev/)!

```capy
to_print :: "Hello, World!\n";

main :: () -> i32 {
    // prints "Hello, World!" to the screen
    puts(to_print);

    // exit with code 0
    0
};

puts :: (some_text: string) extern; // libc defined
```

Capy files end with `.capy` and a bunch of examples can be found in the `examples` folder.

To get started, install the compiler with the following,

```shell
cargo install --path crates/capy
```

Then to run one or more `.capy` files you can type,

```shell
capy run <file1.capy> <file2.capy> ...
```

You can replace `run` with `build` to output only the final executable.

## Features

Static arrays,

```capy
my_array := [] i32 { 4, 8, 15, 16, 23, 42 };

my_array[2] = 10;
```

Pointers,

```capy
foo := 5;
bar := ^mut foo;

bar^ = 10;
```

First Class Functions,

```capy
add :: (x: i32, y: i32) -> i32 {
    x + y
};

mul :: (x: i32, y: i32) -> i32 {
    x * y
};

apply_2_and_3 :: (fun: (x: i32, y: i32) -> i32) -> i32 {
    fun(2, 3)
};

apply_2_and_3(add);
apply_2_and_3(mul);
```

... All compiled to machine code (I'm so proud of this).

Look at the `examples` folder to see more.

## Limitations

If you want to use libc functions, define them with `extern` as above.
Varargs do not work, but this can be worked around,
e.g. by explicitly defining `printf` to take 3 arguments.

You have to manually include all the files your code references in the `capy` command, although this might change in the future.
Frankly, a lot of this might change in the future.

Currently, `gcc` must be installed for the compiler to work.

## Shout Outs

Big shout out to [Luna Razzaghipour](https://github.com/lunacookies), this entire codebase is largely ripped from [gingerbread](https://github.com/gingerbread-lang/gingerbread)/[eldiro](https://github.com/lunacookies/eldiro), although I added a lot more.

Big shout out to [cranelift](https://cranelift.dev/). Trying to get LLVM on windows was just way too much effort for me and you guys made all my dreams come true.
Although you need to up your documentation game, because I mean c'mon man; I pretty much only had the [jit demo](https://github.com/bytecodealliance/cranelift-jit-demo/) to work with.

If anyone wants to use this repo to see how I've implemented higher-level features such as strings, arrays, etc. in cranelift, then it's all in `crates/codegen`.

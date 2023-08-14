# Capy

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

puts :: (some_text: string) -> extern; // libc defined
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

## Extra Notes

You have to manually include all the files your code references in the `capy` command, although this might change in the future.
Frankly, a lot of this might change in the future.

Currently, `gcc` must be installed for the compiler to work.

## Shout Outs

Big shout out to [Luna Razzaghipour](https://github.com/lunacookies), this entire codebase is largely ripped from [gingerbread](https://github.com/gingerbread-lang/gingerbread)/[eldiro](https://github.com/lunacookies/eldiro), although I added a lot more.

Big shout out to cranelift. Trying to get LLVM on windows was just way too much effort for me and you guys made all my dreams come true.
Although you need to up your documentation game, because I mean c'mon man; I pretty much only had the [jit demo](https://github.com/bytecodealliance/cranelift-jit-demo/) to work with.
If you want to use this repo to see how I've implemented higher-level features such as strings, arrays, etc., then it's all in `crates/codegen`.

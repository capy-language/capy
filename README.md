# Capy

A cool programming language

```capy
to_print : string = "Hello, World!\n";

main :: () -> i32 {
    // prints "Hello, World!" to the screen
    printf(to_print);

    // exit with code 0
    0
};

printf :: (some_text: string) -> {
    // libc defined
};
```

Capy files end with `.capy` and some examples can be found in the `examples` folder.

To get started, install the compiler with the following,

```shell
cargo install --path crates/capy
```

Then to run one or more `.capy` files you can type,

```shell
capy run <file1.capy> <file2.capy> ...
```

You can replace `run` with `build` to output only the executable.

## Extra Notes

You have to manually include all the files your code references, although this might change in the future.
Frankly, a lot of this might change in the future.

Currently, `llvm` and `gcc` must be installed for the compiler to work.
The compiler has not been tested on windows.

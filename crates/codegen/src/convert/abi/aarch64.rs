// copied from rustc(https://github.com/rust-lang/rust/blob/master/compiler/rustc_target/src/abi/call/aarch64.rs) for now

#[derive(Copy, Clone, PartialEq)]
pub enum AbiKind {
    AAPCS,
    DarwinPCS,
    Win64,
}


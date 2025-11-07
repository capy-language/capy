//! There are a lot of commonly used structs used after `hir`
//! Especially considering types and the very interlinked relationship of `codegen`
//! and `hir_ty` (they're practically circular dependencies)
//!
//! As such I put a lot of those important ones here in `hir`, even if they don't fit
//! exactly with `hir` or aren't used in `hir`.
//!
//! It's easier to do this than to do weird transmutations

mod locations;
mod names;
mod ty;

pub use locations::*;
pub use names::*;
pub use ty::*;

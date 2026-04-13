/// Ahead-of-time crate compilation and object emission.
mod aot;

pub(crate) use aot::{codegen_crate, join_codegen};

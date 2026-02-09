//! tuffy_target_x86: x86 backend (i386 + x86-64).

pub mod emit;
pub mod encode;
pub mod inst;
pub mod isel;
pub mod reg;

#[cfg(test)]
mod tests;

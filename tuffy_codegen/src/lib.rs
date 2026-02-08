//! tuffy_codegen: Instruction selection, register allocation, and machine code emission.

pub mod emit;
pub mod encode;
pub mod isel;

#[cfg(test)]
mod tests;

//! tuffy_ir: Core intermediate representation for the tuffy compiler.

pub mod builder;
pub mod display;
pub mod function;
pub mod instruction;
pub mod types;
pub mod value;

#[cfg(test)]
mod tests;

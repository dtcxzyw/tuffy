//! tuffy_opt: Optimization pipeline and pass infrastructure.

mod peephole;

pub use peephole::{PeepholeStats, generated_rule_count, optimize_function, optimize_module};

#[cfg(test)]
mod tests;

//! tuffy_opt: Optimization pipeline and pass infrastructure.

mod peephole;

pub use peephole::{
    PeepholeLoadError, PeepholeRuleSet, PeepholeStats, default_rule_set, optimize_function,
    optimize_module,
};

#[cfg(test)]
mod tests;

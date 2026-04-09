//! tuffy_opt: Optimization pipeline and pass infrastructure.

mod peephole;
mod promote;

use tuffy_ir::function::Function;
use tuffy_ir::module::Module;

pub use peephole::{PeepholeStats, generated_rule_count};

pub fn optimize_function(func: &mut Function) -> PeepholeStats {
    let mut stats = promote::promote_function(func);
    stats.merge(peephole::optimize_function(func));
    stats
}

pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let mut total = PeepholeStats::default();
    for func in &mut module.functions {
        total.merge(optimize_function(func));
    }
    total
}

#[cfg(test)]
mod tests;

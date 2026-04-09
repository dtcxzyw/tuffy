//! tuffy_opt: Optimization pipeline and pass infrastructure.

mod inline;
mod peephole;
mod promote;

use tuffy_ir::function::Function;
use tuffy_ir::module::Module;

pub use peephole::{PeepholeStats, generated_rule_count};

pub fn optimize_function(func: &mut Function) -> PeepholeStats {
    run_local_cleanup(func)
}

pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let mut total = PeepholeStats::default();
    for func in &mut module.functions {
        total.merge(run_local_cleanup(func));
    }

    let inline_result = inline::inline_module(module);
    total.merge(inline_result.stats);

    if total.inlined_calls > 0 {
        for (idx, func) in module.functions.iter_mut().enumerate() {
            if inline_result.changed_functions[idx] {
                total.merge(run_local_cleanup(func));
            }
        }
    }
    total
}

fn run_local_cleanup(func: &mut Function) -> PeepholeStats {
    let mut stats = promote::promote_function(func);
    stats.merge(peephole::optimize_function(func));
    stats
}

#[cfg(test)]
mod tests;

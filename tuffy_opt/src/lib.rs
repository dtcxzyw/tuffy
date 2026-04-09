//! tuffy_opt: Optimization pipeline and pass infrastructure.

mod bulk_memory;
mod cfg;
mod cfg_cleanup;
mod inline;
mod peephole;
mod promote;
mod range;

use tuffy_ir::function::Function;
use tuffy_ir::module::Module;

pub use peephole::{PeepholeStats, generated_rule_count};

pub fn optimize_function(func: &mut Function) -> PeepholeStats {
    run_local_cleanup(func)
}

pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let mut total = run_module_cleanup(module, None);

    let inline_result = inline::inline_module(module);
    total.merge(inline_result.stats);

    if total.inlined_calls > 0 {
        total.merge(run_module_cleanup(
            module,
            Some(&inline_result.changed_functions),
        ));
    }
    total
}

fn run_local_cleanup(func: &mut Function) -> PeepholeStats {
    const MAX_LOCAL_CLEANUP_ROUNDS: usize = 8;

    let mut total = PeepholeStats::default();
    for _ in 0..MAX_LOCAL_CLEANUP_ROUNDS {
        let mut round = promote::promote_function(func);
        round.merge(peephole::optimize_function(func));
        round.merge(range::optimize_function(func));
        round.merge(cfg_cleanup::optimize_function(func));
        let changed = round.rewrites > 0
            || round.promoted_slots > 0
            || round.promoted_slices > 0
            || round.promoted_loads > 0
            || round.eliminated_stores > 0;
        total.merge(round);
        if !changed {
            break;
        }
    }
    total
}

fn run_module_cleanup(module: &mut Module, changed_functions: Option<&[bool]>) -> PeepholeStats {
    const MAX_MODULE_CLEANUP_ROUNDS: usize = 6;

    let mut total = PeepholeStats::default();
    for _ in 0..MAX_MODULE_CLEANUP_ROUNDS {
        let mut changed = false;
        for (idx, func) in module.functions.iter_mut().enumerate() {
            if changed_functions.is_some_and(|flags| !flags[idx]) {
                continue;
            }
            let round = run_local_cleanup(func);
            changed |= round.rewrites > 0
                || round.promoted_slots > 0
                || round.promoted_slices > 0
                || round.promoted_loads > 0
                || round.eliminated_stores > 0;
            total.merge(round);
        }

        let bulk = bulk_memory::optimize_module(module, changed_functions);
        changed |= bulk.rewrites > 0;
        total.merge(bulk);

        if !changed {
            break;
        }
    }
    total
}

#[cfg(test)]
mod tests;

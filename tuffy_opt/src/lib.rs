//! tuffy_opt: Optimization pipeline and pass infrastructure.

/// Optimization module `bulk_memory`.
mod bulk_memory;
/// Optimization module `cfg`.
mod cfg;
/// Optimization module `cfg_cleanup`.
mod cfg_cleanup;
/// Optimization module `inline`.
mod inline;
/// Optimization module `peephole`.
mod peephole;
/// Optimization module `promote`.
mod promote;
/// Optimization module `scalar_swap`.
mod scalar_swap;
/// Optimization module `tailrec`.
mod tailrec;

use std::time::Instant;
use tuffy_ir::function::Function;
use tuffy_ir::module::Module;

pub use peephole::{PeepholeStats, generated_rule_count};

/// Generated cleanup pass count.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn generated_cleanup_pass_count() -> usize {
    GENERATED_LOCAL_CLEANUP_PASS_COUNT + GENERATED_MODULE_CLEANUP_PASS_COUNT
}

/// Generated verified cleanup pass count.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn generated_verified_cleanup_pass_count() -> usize {
    GENERATED_VERIFIED_CLEANUP_PASS_COUNT
}

/// Generated legacy cleanup pass count.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn generated_legacy_cleanup_pass_count() -> usize {
    GENERATED_LEGACY_CLEANUP_PASS_COUNT
}

/// Optimize function.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn optimize_function(func: &mut Function) -> PeepholeStats {
    run_local_cleanup(func)
}

/// Optimize module.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
pub fn optimize_module(module: &mut Module) -> PeepholeStats {
    let trace_timings = std::env::var_os("TUFFY_TRACE_TIMINGS").is_some();
    let mut total = run_module_cleanup(module, None);
    if trace_timings {
        eprintln!(
            "[tuffy-timing] module={} phase=module_cleanup_initial rewrites={} promoted_slots={} promoted_slices={} promoted_loads={} eliminated_stores={}",
            module.name,
            total.rewrites,
            total.promoted_slots,
            total.promoted_slices,
            total.promoted_loads,
            total.eliminated_stores
        );
    }

    let inline_result = inline::inline_module(module);
    total.merge(inline_result.stats);
    if trace_timings {
        eprintln!(
            "[tuffy-timing] module={} phase=inline iterations={} inlined_calls={}",
            module.name, total.inline_iterations, total.inlined_calls
        );
    }

    if total.inlined_calls > 0 {
        let cleanup = run_module_cleanup(module, Some(&inline_result.changed_functions));
        if trace_timings {
            eprintln!(
                "[tuffy-timing] module={} phase=module_cleanup_post_inline rewrites={} promoted_slots={} promoted_slices={} promoted_loads={} eliminated_stores={}",
                module.name,
                cleanup.rewrites,
                cleanup.promoted_slots,
                cleanup.promoted_slices,
                cleanup.promoted_loads,
                cleanup.eliminated_stores
            );
        }
        total.merge(cleanup);
    }
    total
}

/// Internal helper `run_local_cleanup`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn run_local_cleanup(func: &mut Function) -> PeepholeStats {
    /// Internal constant `MAX_LOCAL_CLEANUP_ROUNDS`.
    const MAX_LOCAL_CLEANUP_ROUNDS: usize = 8;

    let mut total = PeepholeStats::default();
    for _ in 0..MAX_LOCAL_CLEANUP_ROUNDS {
        let round = run_generated_local_cleanup_passes(func);
        let tailrec = tailrec::optimize_function(func);
        let changed = round.rewrites > 0
            || tailrec.rewrites > 0
            || round.promoted_slots > 0
            || round.promoted_slices > 0
            || round.promoted_loads > 0
            || round.eliminated_stores > 0;
        total.merge(round);
        total.merge(tailrec);
        if !changed {
            break;
        }
    }
    total
}

/// Internal helper `run_module_cleanup`.
///
/// # Panics
///
/// May panic if internal IR invariants are violated.
fn run_module_cleanup(module: &mut Module, changed_functions: Option<&[bool]>) -> PeepholeStats {
    /// Internal constant `MAX_MODULE_CLEANUP_ROUNDS`.
    const MAX_MODULE_CLEANUP_ROUNDS: usize = 6;

    let trace_timings = std::env::var_os("TUFFY_TRACE_TIMINGS").is_some();
    let mut total = PeepholeStats::default();
    for _ in 0..MAX_MODULE_CLEANUP_ROUNDS {
        let mut changed = false;
        for idx in 0..module.functions.len() {
            if changed_functions.is_some_and(|flags| !flags[idx]) {
                continue;
            }
            let func_name = module.resolve(module.functions[idx].name).to_string();
            let inst_count = module.functions[idx].inst_pool.iter_insts().count();
            let cleanup_start = Instant::now();
            let round = {
                let func = &mut module.functions[idx];
                run_local_cleanup(func)
            };
            let cleanup_elapsed = cleanup_start.elapsed();
            changed |= round.rewrites > 0
                || round.promoted_slots > 0
                || round.promoted_slices > 0
                || round.promoted_loads > 0
                || round.eliminated_stores > 0;
            if trace_timings && cleanup_elapsed.as_millis() >= 100 {
                eprintln!(
                    "[tuffy-timing] module={} function={} phase=local_cleanup insts={} elapsed_ms={} rewrites={} iterations={} promoted_slots={} promoted_slices={} promoted_loads={} eliminated_stores={}",
                    module.name,
                    func_name,
                    inst_count,
                    cleanup_elapsed.as_millis(),
                    round.rewrites,
                    round.iterations,
                    round.promoted_slots,
                    round.promoted_slices,
                    round.promoted_loads,
                    round.eliminated_stores
                );
            }
            total.merge(round);
        }

        let module_round = run_generated_module_cleanup_passes(module, changed_functions);
        changed |= module_round.rewrites > 0;
        total.merge(module_round);

        if !changed {
            break;
        }
    }
    total
}

#[cfg(test)]
/// Optimization module `tests`.
mod tests;

include!(concat!(env!("OUT_DIR"), "/cleanup_pass_manifest_gen.rs"));

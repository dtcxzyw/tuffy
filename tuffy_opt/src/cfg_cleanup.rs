use std::collections::{HashMap, HashSet};

use tuffy_ir::function::Function;
use tuffy_ir::instruction::{Op, Operand};
use tuffy_ir::value::{BlockRef, ValueRef};

use crate::cfg::{CfgInfo, collect_block_refs};
use crate::peephole::PeepholeStats;

const MAX_CLEANUP_ITERATIONS: usize = 8;

pub(crate) fn optimize_function(func: &mut Function) -> PeepholeStats {
    if func
        .inst_pool
        .iter_insts()
        .any(|(_, inst)| matches!(inst.op, Op::Continue(_) | Op::RegionYield(_)))
    {
        return PeepholeStats::default();
    }

    let mut stats = PeepholeStats::default();

    for _ in 0..MAX_CLEANUP_ITERATIONS {
        let mut changed = false;

        if thread_forwarders(func) {
            func.rebuild_use_lists();
            stats.record("cfg_thread_forwarders");
            changed = true;
        }

        if !changed {
            break;
        }
    }

    stats
}

fn thread_forwarders(func: &mut Function) -> bool {
    let cfg = CfgInfo::compute(func);
    let forwarders = compute_forwarders(func, &cfg);
    if forwarders.is_empty() {
        return false;
    }

    let mut changed = false;
    let block_refs = collect_block_refs(func);
    for block in block_refs {
        if !cfg.reachable[block.index() as usize] {
            continue;
        }
        let Some(last_idx) = func.block(block).last_inst else {
            continue;
        };
        let Some(old_node) = func.inst_pool.get(last_idx) else {
            continue;
        };
        let new_op = match &old_node.inst.op {
            Op::Br(target, args) => {
                let (resolved_target, resolved_args) =
                    resolve_forward_target(func, &forwarders, block, *target, args.clone());
                if resolved_target != *target || !operands_eq(&resolved_args, args) {
                    Some(Op::Br(resolved_target, resolved_args))
                } else {
                    None
                }
            }
            Op::BrIf(cond, then_block, then_args, else_block, else_args) => {
                let (new_then, new_then_args) = resolve_forward_target(
                    func,
                    &forwarders,
                    block,
                    *then_block,
                    then_args.clone(),
                );
                let (new_else, new_else_args) = resolve_forward_target(
                    func,
                    &forwarders,
                    block,
                    *else_block,
                    else_args.clone(),
                );
                if (new_then == new_else && operands_eq(&new_then_args, &new_else_args))
                    || new_then != *then_block
                    || new_else != *else_block
                    || !operands_eq(&new_then_args, then_args)
                    || !operands_eq(&new_else_args, else_args)
                {
                    if new_then == new_else && operands_eq(&new_then_args, &new_else_args) {
                        Some(Op::Br(new_then, new_then_args))
                    } else {
                        Some(Op::BrIf(
                            cond.clone(),
                            new_then,
                            new_then_args,
                            new_else,
                            new_else_args,
                        ))
                    }
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(new_op) = new_op {
            func.inst_pool.inst_mut(last_idx).op = new_op;
            changed = true;
        }
    }

    changed
}

#[derive(Clone)]
struct Forwarder {
    target: BlockRef,
    args: Vec<Operand>,
}

fn compute_forwarders(func: &Function, cfg: &CfgInfo) -> HashMap<BlockRef, Forwarder> {
    let entry = func.entry_block();
    let region_entries = func
        .regions
        .iter()
        .map(|region| region.entry_block)
        .collect::<HashSet<_>>();

    let mut forwarders = HashMap::new();
    for block in collect_block_refs(func) {
        if !cfg.reachable[block.index() as usize]
            || block == entry
            || region_entries.contains(&block)
        {
            continue;
        }
        let bb = func.block(block);
        if bb.inst_count != 1 {
            continue;
        }
        let Some(last_idx) = bb.last_inst else {
            continue;
        };
        let inst = func.inst(last_idx);
        let Op::Br(target, args) = &inst.op else {
            continue;
        };
        if func.block(*target).parent_region != bb.parent_region {
            continue;
        }
        if args.len() != bb.arg_count as usize {
            continue;
        }
        forwarders.insert(
            block,
            Forwarder {
                target: *target,
                args: args.clone(),
            },
        );
    }
    forwarders
}

fn resolve_forward_target(
    func: &Function,
    forwarders: &HashMap<BlockRef, Forwarder>,
    source_block: BlockRef,
    mut target: BlockRef,
    mut args: Vec<Operand>,
) -> (BlockRef, Vec<Operand>) {
    let source_region = func.block(source_block).parent_region;
    let mut seen = HashSet::new();

    while let Some(forwarder) = forwarders.get(&target) {
        if !seen.insert(target) {
            break;
        }
        if func.block(target).parent_region != source_region {
            break;
        }

        let arg_map = func
            .block_arg_values(target)
            .into_iter()
            .zip(args.iter().cloned())
            .collect::<HashMap<_, _>>();
        args = forwarder
            .args
            .iter()
            .map(|operand| remap_forward_operand(operand, &arg_map))
            .collect();
        target = forwarder.target;
    }

    (target, args)
}

fn remap_forward_operand(operand: &Operand, arg_map: &HashMap<ValueRef, Operand>) -> Operand {
    arg_map
        .get(&operand.value)
        .cloned()
        .unwrap_or_else(|| operand.clone())
}

fn operands_eq(lhs: &[Operand], rhs: &[Operand]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs.iter())
            .all(|(lhs, rhs)| lhs.value == rhs.value && lhs.annotation == rhs.annotation)
}

use std::collections::HashSet;

use tuffy_ir::function::Function;
use tuffy_ir::value::BlockRef;

#[derive(Clone, Debug)]
pub(crate) struct CfgInfo {
    pub(crate) preds: Vec<Vec<BlockRef>>,
    pub(crate) succs: Vec<Vec<BlockRef>>,
    pub(crate) reachable: Vec<bool>,
    pub(crate) dom_children: Vec<Vec<BlockRef>>,
    pub(crate) dominance_frontier: Vec<HashSet<BlockRef>>,
    pub(crate) loop_header: Vec<Option<BlockRef>>,
}

impl CfgInfo {
    pub(crate) fn compute(func: &Function) -> Self {
        let block_count = func.blocks.len();
        let block_refs = collect_block_refs(func);
        let mut succs = vec![Vec::new(); block_count];
        let mut loop_header = vec![None; block_count];

        for block_idx in 0..block_count {
            let block = block_refs[block_idx];
            let Some(last_idx) = func.block(block).last_inst else {
                continue;
            };
            let inst = func.inst(last_idx);
            let mut add_succ = |target: BlockRef| {
                if !succs[block_idx].contains(&target) {
                    succs[block_idx].push(target);
                }
            };
            match &inst.op {
                tuffy_ir::instruction::Op::Br(target, _) => add_succ(*target),
                tuffy_ir::instruction::Op::BrIf(_, then_block, _, else_block, _) => {
                    add_succ(*then_block);
                    add_succ(*else_block);
                }
                tuffy_ir::instruction::Op::Continue(_) => {
                    if let Some(header) = loop_header_for_block(func, block) {
                        add_succ(header);
                        loop_header[block_idx] = Some(header);
                    }
                }
                _ => {}
            }
        }

        let mut preds = vec![Vec::new(); block_count];
        for (from_idx, targets) in succs.iter().enumerate() {
            for target in targets {
                preds[target.index() as usize].push(block_refs[from_idx]);
            }
        }

        let entry = func.entry_block();
        let mut reachable = vec![false; block_count];
        let mut postorder = Vec::new();
        let mut stack = vec![(entry, 0usize)];
        reachable[entry.index() as usize] = true;
        while let Some((block, next_idx)) = stack.pop() {
            let succ_list = &succs[block.index() as usize];
            if next_idx < succ_list.len() {
                stack.push((block, next_idx + 1));
                let succ = succ_list[next_idx];
                if !reachable[succ.index() as usize] {
                    reachable[succ.index() as usize] = true;
                    stack.push((succ, 0));
                }
            } else {
                postorder.push(block);
            }
        }
        postorder.reverse();
        let rpo = postorder;

        let mut rpo_pos = vec![usize::MAX; block_count];
        for (idx, block) in rpo.iter().enumerate() {
            rpo_pos[block.index() as usize] = idx;
        }

        let mut idom = vec![None; block_count];
        idom[entry.index() as usize] = Some(entry);
        let mut changed = true;
        while changed {
            changed = false;
            for block in rpo.iter().copied().skip(1) {
                let pred_list = preds[block.index() as usize]
                    .iter()
                    .copied()
                    .filter(|pred| {
                        reachable[pred.index() as usize] && idom[pred.index() as usize].is_some()
                    })
                    .collect::<Vec<_>>();
                let Some((first_pred, rest)) = pred_list.split_first() else {
                    continue;
                };
                let mut new_idom = *first_pred;
                for pred in rest {
                    new_idom = intersect_idom(&idom, &rpo_pos, *pred, new_idom);
                }
                if idom[block.index() as usize] != Some(new_idom) {
                    idom[block.index() as usize] = Some(new_idom);
                    changed = true;
                }
            }
        }

        let mut dom_children = vec![Vec::new(); block_count];
        for block in rpo.iter().copied().skip(1) {
            if let Some(parent) = idom[block.index() as usize] {
                dom_children[parent.index() as usize].push(block);
            }
        }

        let mut dominance_frontier = vec![HashSet::new(); block_count];
        for block in rpo.iter().copied() {
            let pred_list = preds[block.index() as usize]
                .iter()
                .copied()
                .filter(|pred| reachable[pred.index() as usize])
                .collect::<Vec<_>>();
            if pred_list.len() < 2 {
                continue;
            }
            let Some(block_idom) = idom[block.index() as usize] else {
                continue;
            };
            for pred in pred_list {
                let mut runner = pred;
                while runner != block_idom {
                    dominance_frontier[runner.index() as usize].insert(block);
                    let Some(next) = idom[runner.index() as usize] else {
                        break;
                    };
                    runner = next;
                }
            }
        }

        Self {
            preds,
            succs,
            reachable,
            dom_children,
            dominance_frontier,
            loop_header,
        }
    }
}

pub(crate) fn collect_block_refs(func: &Function) -> Vec<BlockRef> {
    let mut refs = vec![None; func.blocks.len()];
    for region in &func.regions {
        for child in &region.children {
            if let tuffy_ir::function::CfgNode::Block(block) = child {
                refs[block.index() as usize] = Some(*block);
            }
        }
    }
    refs.into_iter()
        .map(|block| block.expect("every block should appear in a region"))
        .collect()
}

pub(crate) fn has_unwind_cleanup_edges(func: &Function) -> bool {
    func.inst_pool
        .iter_insts()
        .any(|(_, inst)| matches!(inst.op, tuffy_ir::instruction::Op::Call(_, _, _, Some(_))))
}

pub(crate) fn loop_header_for_block(func: &Function, block: BlockRef) -> Option<BlockRef> {
    let mut region = func.block(block).parent_region;
    loop {
        let current = func.region(region);
        if current.kind == tuffy_ir::function::RegionKind::Loop {
            return Some(current.entry_block);
        }
        region = current.parent?;
    }
}

fn intersect_idom(
    idom: &[Option<BlockRef>],
    rpo_pos: &[usize],
    mut lhs: BlockRef,
    mut rhs: BlockRef,
) -> BlockRef {
    while lhs != rhs {
        while rpo_pos[lhs.index() as usize] > rpo_pos[rhs.index() as usize] {
            lhs = idom[lhs.index() as usize].expect("reachable block should have idom");
        }
        while rpo_pos[rhs.index() as usize] > rpo_pos[lhs.index() as usize] {
            rhs = idom[rhs.index() as usize].expect("reachable block should have idom");
        }
    }
    lhs
}

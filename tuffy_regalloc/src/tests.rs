//! Unit tests for liveness analysis and linear scan allocator.

use crate::allocator::allocate;
use crate::liveness::compute_live_ranges;
use crate::{OpKind, PReg, RegAllocInst, RegOp, VReg};

/// Simple test instruction for unit tests.
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum TInst {
    /// def dst
    Def { dst: VReg },
    /// use src
    Use { src: VReg },
    /// dst = src (def dst, use src)
    Mov { dst: VReg, src: VReg },
    /// dst += src (usedef dst, use src)
    Add { dst: VReg, src: VReg },
    /// label
    Label { id: u32 },
    /// unconditional jump
    Jmp { target: u32 },
    /// conditional branch (falls through)
    Jcc { target: u32 },
    /// return
    Ret,
}

impl RegAllocInst for TInst {
    fn reg_operands(&self, ops: &mut Vec<RegOp>) {
        match self {
            TInst::Def { dst } => ops.push(RegOp {
                vreg: *dst,
                kind: OpKind::Def,
            }),
            TInst::Use { src } => ops.push(RegOp {
                vreg: *src,
                kind: OpKind::Use,
            }),
            TInst::Mov { dst, src } => {
                ops.push(RegOp {
                    vreg: *dst,
                    kind: OpKind::Def,
                });
                ops.push(RegOp {
                    vreg: *src,
                    kind: OpKind::Use,
                });
            }
            TInst::Add { dst, src } => {
                ops.push(RegOp {
                    vreg: *dst,
                    kind: OpKind::UseDef,
                });
                ops.push(RegOp {
                    vreg: *src,
                    kind: OpKind::Use,
                });
            }
            TInst::Label { .. } | TInst::Jmp { .. } | TInst::Jcc { .. } | TInst::Ret => {}
        }
    }

    fn label_id(&self) -> Option<u32> {
        match self {
            TInst::Label { id } => Some(*id),
            _ => None,
        }
    }

    fn branch_targets(&self, targets: &mut Vec<u32>) {
        match self {
            TInst::Jmp { target } | TInst::Jcc { target } => targets.push(*target),
            _ => {}
        }
    }

    fn clobbers(&self, _clobbers: &mut Vec<PReg>) {}

    fn is_terminator(&self) -> bool {
        matches!(self, TInst::Ret | TInst::Jmp { .. } | TInst::Jcc { .. })
    }

    fn falls_through(&self) -> bool {
        !matches!(self, TInst::Ret | TInst::Jmp { .. })
    }
}

fn v(n: u32) -> VReg {
    VReg(n)
}

// --- Liveness tests ---

#[test]
fn liveness_simple_straight_line() {
    // v0 = def; v1 = def; v2 = v0 + v1; use v2; ret
    let insts = vec![
        TInst::Def { dst: v(0) },
        TInst::Def { dst: v(1) },
        TInst::Add {
            dst: v(0),
            src: v(1),
        },
        TInst::Use { src: v(0) },
        TInst::Ret,
    ];
    let ranges = compute_live_ranges(&insts, 2);

    assert_eq!(ranges.len(), 2);
    // v0: defined at 0, last used at 3 → [0, 4)
    let r0 = ranges.iter().find(|r| r.vreg == v(0)).unwrap();
    assert_eq!(r0.start, 0);
    assert_eq!(r0.end, 4);
    // v1: defined at 1, last used at 2 → [1, 3)
    let r1 = ranges.iter().find(|r| r.vreg == v(1)).unwrap();
    assert_eq!(r1.start, 1);
    assert_eq!(r1.end, 3);
}

#[test]
fn liveness_branch() {
    // entry: v0 = def; jcc L1
    // L1: use v0; ret
    let insts = vec![
        TInst::Def { dst: v(0) },
        TInst::Jcc { target: 1 },
        TInst::Label { id: 1 },
        TInst::Use { src: v(0) },
        TInst::Ret,
    ];
    let ranges = compute_live_ranges(&insts, 1);

    assert_eq!(ranges.len(), 1);
    let r0 = ranges.iter().find(|r| r.vreg == v(0)).unwrap();
    // v0 must be live from def (0) through use (3) → [0, 4)
    assert_eq!(r0.start, 0);
    assert!(r0.end >= 4);
}

#[test]
fn liveness_empty() {
    let ranges = compute_live_ranges::<TInst>(&[], 0);
    assert!(ranges.is_empty());
}

// --- Allocator tests ---

#[test]
fn alloc_simple_no_conflicts() {
    // Two non-overlapping VRegs, 2 registers available.
    let insts = vec![
        TInst::Def { dst: v(0) },
        TInst::Use { src: v(0) },
        TInst::Def { dst: v(1) },
        TInst::Use { src: v(1) },
        TInst::Ret,
    ];
    let constraints = vec![None, None];
    let regs = vec![PReg(0), PReg(1)];
    let result = allocate(&insts, 2, &constraints, &regs, &[], PReg(2));

    assert_eq!(result.assignments.len(), 2);
    // Both should get valid registers from the pool.
    assert!(regs.contains(&result.assignments[0]));
    assert!(regs.contains(&result.assignments[1]));
}

#[test]
fn alloc_fixed_constraint() {
    // v0 must be in PReg(1), v1 is free.
    let insts = vec![
        TInst::Def { dst: v(0) },
        TInst::Mov {
            dst: v(1),
            src: v(0),
        },
        TInst::Use { src: v(1) },
        TInst::Ret,
    ];
    let constraints = vec![Some(PReg(1)), None];
    let regs = vec![PReg(0), PReg(1)];
    let result = allocate(&insts, 2, &constraints, &regs, &[], PReg(2));

    assert_eq!(result.assignments[0], PReg(1));
    assert!(regs.contains(&result.assignments[1]));
}

#[test]
fn alloc_overlapping_intervals() {
    // v0 and v1 are live at the same time — need different registers.
    let insts = vec![
        TInst::Def { dst: v(0) },
        TInst::Def { dst: v(1) },
        TInst::Use { src: v(0) },
        TInst::Use { src: v(1) },
        TInst::Ret,
    ];
    let constraints = vec![None, None];
    let regs = vec![PReg(0), PReg(1)];
    let result = allocate(&insts, 2, &constraints, &regs, &[], PReg(2));

    assert_eq!(result.assignments.len(), 2);
    // They must get different registers since they overlap.
    assert_ne!(result.assignments[0], result.assignments[1]);
}

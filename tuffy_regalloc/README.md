# tuffy_regalloc

Target-agnostic register allocator.

## Design

Linear scan register allocator that operates on virtual registers (`VReg`) and rewrites them to physical registers (`PReg`). Backends integrate by implementing the `RegAllocInst` and `RegAllocTarget` traits.

### Core Types

- `VReg(u32)` — virtual register produced by instruction selection.
- `PReg(u8)` — physical register (hardware encoding, e.g., 0..15 for x86-64 GPRs).
- `OpKind` — operand kind: `Use`, `Def`, or `UseDef`.
- `RegOp` — a register operand declaration (vreg + kind).

### RegAllocInst Trait

Instructions implement `RegAllocInst` to declare:
- Register operands (`reg_operands`)
- Label IDs for pseudo-label instructions (`label_id`)
- Branch targets (`branch_targets`)
- Clobbered physical registers (`clobbers`) — for call instructions
- Terminator and fall-through properties

## Liveness Analysis (`liveness.rs`)

Computes live ranges by:
1. Building a CFG from the linear instruction list (splitting at labels and terminators).
2. Running backward dataflow to compute per-block `live_in` / `live_out` sets.
3. Merging into per-VReg `[start, end)` intervals.

## Linear Scan Allocator (`allocator.rs`)

- Assigns physical registers using live range intervals.
- Respects fixed-register constraints from instruction selection.
- Spills to stack slots when register pressure exceeds available registers.
- Values live across calls are assigned to callee-saved registers only.
- Reports `AllocResult`: assignments, spill slots, used callee-saved registers, and spill map.

## Dependencies

None (standalone crate).

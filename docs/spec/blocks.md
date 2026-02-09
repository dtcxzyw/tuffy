# Basic Blocks

A basic block is a straight-line sequence of instructions with no internal control flow.
Blocks are named `bb0`, `bb1`, etc. in text format.

## Block Arguments

Tuffy IR uses block arguments instead of PHI nodes to represent values that merge at
control flow join points. Block arguments are declared in the block header and receive
values from predecessor branches:

```
bb0:
  v0 = iconst 1
  br bb1(v0)

bb1(v1: int):       // v1 is a block argument
  ret v1
```

Each branch instruction (`br`, `brif`, `continue`) passes values to the target block's
arguments. The number and types of passed values must match the target block's argument
list.

## Instruction Ordering

Instructions within a block execute sequentially. The last instruction in a block must
be a terminator (`ret`, `br`, `brif`, `continue`, `region_yield`).

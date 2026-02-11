# Implement Generic Linear Scan Register Allocator

- Status: Completed
- Created: 2026-02-10
- Completed: 2026-02-11
- Parent: N/A

## Description

Implement a generic (target-agnostic) linear scan register allocator in tuffy codegen, replacing the current simple round-robin allocation strategy in `tuffy_target_x86`.

### Background

The current x86 backend register allocation (`RegAlloc` in `tuffy_target_x86/src/isel.rs`) uses a simple round-robin scheme, cycling through 9 caller-saved registers and spilling directly to stack slots when exhausted. This approach has the following problems:

- No awareness of value liveness, leading to unnecessary spills.
- Cannot handle register pressure, producing inefficient code in complex functions.
- Does not consider use frequency or distance, preventing reasonable spill decisions.
- Coupled with instruction selection, making it difficult to reuse across backends.

### Goal

Implement a linear scan-based register allocator as an independent, target-agnostic module that can be reused across different backends.

### Core Features

1. **Liveness Analysis**
   - Compute live intervals (live ranges) for each virtual register.
   - Support interval representation based on linearized instruction sequences.
   - Handle live intervals for block arguments (replacing PHI nodes).

2. **Linear Scan Allocation**
   - Sort by live interval start position and linearly scan to assign physical registers.
   - Maintain an active list (intervals currently occupying registers) and an inactive list.
   - When registers are insufficient, select spill candidates using heuristics (e.g., furthest next use).

3. **Spilling**
   - Allocate stack slots for spilled values.
   - Insert load/store instructions at spill points.
   - Support spill weight computation (based on loop depth, use frequency, etc.).

4. **Target Abstraction Interface**
   - Define a `RegAllocTarget` trait; backends provide:
     - Allocatable register sets (by register class: GPR, FPR, etc.).
     - Instruction register constraints (fixed registers, early clobber, etc.).
     - Calling convention information (caller-saved / callee-saved).
   - x86-64 backend implements this trait.

5. **Move Resolution**
   - Handle parallel moves arising from block argument passing.
   - Implement move serialization (resolve cyclic dependencies, using temporary registers when necessary).

### Design Notes

- The allocator should be an independent module in `tuffy_codegen` or a new `tuffy_regalloc` crate.
- Input: instruction sequence in virtual register form + register constraints. Output: physical register assignment.
- The isel stage must first be changed to emit virtual registers, then the regalloc pass maps them to physical registers.
- References: Poletto & Sarkar 1999 "Linear Scan Register Allocation", and subsequent improvements (Second Chance Binpacking, etc.).

## Subtasks

- Design the regalloc module interface and data structures (virtual registers, live intervals, register constraints)
- Implement liveness analysis
- Implement the core linear scan allocation algorithm
- Implement spilling (stack slot allocation, load/store insertion)
- Define the `RegAllocTarget` trait and implement it for x86-64
- Implement parallel move resolution
- Refactor the isel stage to emit virtual registers instead of directly assigning physical registers
- Integrate into the compilation pipeline and add tests

## Affected Modules

- `tuffy_codegen` — Add generic regalloc module (or create a new `tuffy_regalloc` crate)
- `tuffy_target` — Extend the `Backend` trait or add a new `RegAllocTarget` trait
- `tuffy_target_x86` — Refactor isel to emit virtual registers, implement the target interface, remove the old round-robin allocation

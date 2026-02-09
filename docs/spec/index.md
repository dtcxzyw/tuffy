# Tuffy IR Language Reference

This document is the reference manual for the Tuffy IR, the intermediate representation
used by the tuffy compiler. It describes the type system, instruction set, control flow
structure, and textual format of the IR.

> **Status**: This spec describes the currently implemented IR. Features described in
> the [IR Design RFC](../RFCs/202602/ir-design.md) but not yet implemented are noted as
> *planned*.
>
> **Source of truth**: The formal definitions in Lean 4 (`lean/TuffyLean/IR/`) are
> authoritative. This spec is a human-readable description that must conform to the
> Lean definitions. When in doubt, consult the Lean code.

## Introduction

Tuffy IR is a typed, SSA-based intermediate representation organized around a
hierarchical control flow graph with SESE (Single Entry, Single Exit) regions.

Key design principles:

- **Infinite precision integers** — no fixed bit widths; range constraints via assert nodes
- **Block arguments** instead of PHI nodes (Cranelift/MLIR style)
- **Hierarchical CFG** — loops and structured control flow are explicit SESE regions
- **Poison-only UB model** — no `undef`; only `poison`
- **Single data structure** — one IR across all compilation stages

## Table of Contents

- [Type System](types.md)
- [Values](values.md)
- [Functions](functions.md)
- [Regions](regions.md)
- [Basic Blocks](blocks.md)
- [Instructions](instructions.md)
  - [Constants](instructions.md#constants)
  - [Arithmetic](instructions.md#arithmetic)
  - [Floating Point Arithmetic](instructions.md#floating-point-arithmetic)
  - [Comparison](instructions.md#comparison)
  - [Value Annotations](instructions.md#value-annotations)
  - [Memory Operations](instructions.md#memory-operations)
  - [Atomic Operations](instructions.md#atomic-operations)
  - [Type Conversion](instructions.md#type-conversion)
  - [Pointer Operations](instructions.md#pointer-operations)
  - [Function Calls](instructions.md#function-calls)
  - [Terminators](instructions.md#terminators)
- [Text Format](text-format.md)
- [Planned Features](planned.md)

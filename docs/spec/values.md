# Values

A value in tuffy IR is one of four kinds, as defined in Lean (`TuffyLean.IR.Value`):

| Kind | Description |
|------|-------------|
| `int(v)` | An infinite precision integer with mathematical value `v` |
| `bytes(bs)` | A sequence of [abstract bytes](#abstract-bytes) |
| `ptr(p)` | A pointer with provenance (allocation ID + offset) |
| `poison` | A poison value — the result of undefined behavior |

## Abstract Bytes

Each byte in memory is represented as an abstract byte (`TuffyLean.IR.AbstractByte`):

| State | Description |
|-------|-------------|
| `bits(val)` | A concrete byte value (0–255) |
| `ptrFragment(allocId, index)` | The `index`-th byte of a pointer to allocation `allocId` |
| `uninit` | Uninitialized memory (a distinct abstract state, not "random bits") |
| `poison` | A poisoned byte |

## Pointers and Provenance

A pointer consists of an allocation ID and an integer offset
(`TuffyLean.IR.Pointer`). The allocation ID tracks which allocation the pointer
belongs to, enabling provenance-based alias analysis.

-- TuffyLean/IR/Types.lean
-- Formal semantics of tuffy IR types

import Mathlib.Data.Int.Basic
import Mathlib.Data.BitVec

namespace TuffyLean.IR

/-- Floating point type variants -/
inductive FloatType where
  | bf16   -- Brain floating point (bfloat16)
  | f16    -- IEEE 754 half precision
  | f32    -- IEEE 754 single precision
  | f64    -- IEEE 754 double precision
  deriving DecidableEq, Repr

/-- Vector type parameterized by total bit-width.
    Element count is derived: count = width / element_bits.
    See RFC: scalable-vectors.md -/
inductive VectorType where
  | fixed (width : Nat)        -- fixed-width vector (e.g., 128 for SSE)
  | scalable (baseWidth : Nat) -- vscale × baseWidth bits (e.g., SVE, RVV)
  deriving DecidableEq, Repr

/-- Well-formedness: vector width must be positive and byte-aligned -/
def VectorType.wellFormed : VectorType → Prop
  | .fixed w => w > 0 ∧ w % 8 = 0
  | .scalable bw => bw > 0 ∧ bw % 8 = 0

/-- Well-formedness with element width: divisible and power-of-two lane count -/
def VectorType.wellFormedWithElement (vt : VectorType) (elemBits : Nat) : Prop :=
  let w := match vt with | .fixed w => w | .scalable bw => bw
  vt.wellFormed ∧ elemBits > 0 ∧ w % elemBits = 0 ∧ Nat.isPowerOfTwo (w / elemBits)

/-- Get the base width in bits -/
def VectorType.baseWidth : VectorType → Nat
  | .fixed w => w
  | .scalable bw => bw

/-- Compute lane count given element bit-width -/
def VectorType.laneCount (vt : VectorType) (elemBits : Nat) : Nat :=
  vt.baseWidth / elemBits

/-- Range annotation on a value definition or use edge -/
inductive Annotation where
  | signed (bits : Nat)    -- :s<N> — value in [-2^(N-1), 2^(N-1)-1]
  | unsigned (bits : Nat)  -- :u<N> — value in [0, 2^N-1]
  deriving DecidableEq, Repr

/-- Abstract allocation identifier for pointer provenance -/
structure AllocId where
  id : Nat
  deriving DecidableEq, Repr

/-- Pointer with provenance -/
structure Pointer where
  allocId : AllocId
  offset : Int
  deriving Repr

/-- Abstract byte: four-state memory model -/
inductive AbstractByte where
  | bits (val : UInt8)
  | ptrFragment (ptr : AllocId) (index : Nat)
  | uninit
  | poison
  deriving Repr

/-- Tuffy IR value -/
inductive Value where
  | int (val : Int)
  | bytes (bs : List AbstractByte)
  | ptr (p : Pointer)
  | poison
  deriving Repr

/-- Memory: a map from addresses to abstract bytes -/
structure Memory where
  bytes : Int → AbstractByte

/-- Memory ordering for atomic operations -/
inductive MemoryOrdering where
  | relaxed
  | acquire
  | release
  | acqrel
  | seqcst
  deriving DecidableEq, Repr

/-- Atomic read-modify-write operation kinds -/
inductive AtomicRmwOp where
  | xchg
  | add
  | sub
  | and
  | or
  | xor
  deriving DecidableEq, Repr

end TuffyLean.IR

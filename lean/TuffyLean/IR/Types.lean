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

/-- IEEE 754 floating-point value classes, mirroring LLVM's FPClassTest.
    Used by `nofpclass` annotations to exclude specific FP classes. -/
inductive FpClass where
  | snan   -- signaling NaN
  | qnan   -- quiet NaN
  | ninf   -- negative infinity
  | nnorm  -- negative normal
  | nsub   -- negative subnormal
  | nzero  -- negative zero
  | pzero  -- positive zero
  | psub   -- positive subnormal
  | pnorm  -- positive normal
  | pinf   -- positive infinity
  deriving DecidableEq, Repr

/-- Bitmask of excluded FP classes. Each field being `true` means that
    class is excluded (value must NOT be in that class). -/
structure FpClassMask where
  snan : Bool := false
  qnan : Bool := false
  ninf : Bool := false
  nnorm : Bool := false
  nsub : Bool := false
  nzero : Bool := false
  pzero : Bool := false
  psub : Bool := false
  pnorm : Bool := false
  pinf : Bool := false
  deriving DecidableEq, Repr

namespace FpClassMask

/-- No classes excluded (empty mask). -/
def none : FpClassMask := {}

/-- Exclude all NaN (snan + qnan). -/
def nan : FpClassMask := { snan := true, qnan := true }

/-- Exclude all infinity (ninf + pinf). -/
def inf : FpClassMask := { ninf := true, pinf := true }

/-- Exclude NaN and infinity. -/
def nanInf : FpClassMask :=
  { snan := true, qnan := true, ninf := true, pinf := true }

/-- Test whether a specific FP class is excluded by this mask. -/
def test (m : FpClassMask) : FpClass → Bool
  | .snan => m.snan
  | .qnan => m.qnan
  | .ninf => m.ninf
  | .nnorm => m.nnorm
  | .nsub => m.nsub
  | .nzero => m.nzero
  | .pzero => m.pzero
  | .psub => m.psub
  | .pnorm => m.pnorm
  | .pinf => m.pinf

/-- Union of two masks (exclude classes from either). -/
def union (a b : FpClassMask) : FpClassMask where
  snan := a.snan || b.snan
  qnan := a.qnan || b.qnan
  ninf := a.ninf || b.ninf
  nnorm := a.nnorm || b.nnorm
  nsub := a.nsub || b.nsub
  nzero := a.nzero || b.nzero
  pzero := a.pzero || b.pzero
  psub := a.psub || b.psub
  pnorm := a.pnorm || b.pnorm
  pinf := a.pinf || b.pinf

end FpClassMask

/-- Rewrite flags for floating-point instructions.
    These are optimization permissions, not value constraints.
    They do not affect operational semantics — only which rewrites are legal. -/
structure FpRewriteFlags where
  reassoc : Bool := false  -- allow associativity/commutativity reordering
  contract : Bool := false  -- allow contraction (e.g., fma fusion)
  deriving DecidableEq, Repr

/-- Range annotation on a value definition or use edge.
    Integer-only; float constraints use `FpClassMask` separately. -/
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
  | bool (val : Bool)
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

/-- Integer comparison predicates.
    Signedness is a property of operand annotations, not the predicate. -/
inductive ICmpOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Interned symbol identifier. Indexes into a module-level symbol table.
    Used for function names, static data labels, and external references. -/
structure SymbolId where
  id : Nat
  deriving DecidableEq, Repr, Hashable

end TuffyLean.IR

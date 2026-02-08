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

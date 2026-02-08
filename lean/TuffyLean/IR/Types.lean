-- TuffyLean/IR/Types.lean
-- Formal semantics of tuffy IR types

import Mathlib.Data.Int.Basic
import Mathlib.Data.BitVec

namespace TuffyLean.IR

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

end TuffyLean.IR

-- TuffyLean/Prototyping/Opt/Fp/Basic.lean
-- Prototype floating-point optimizations to validate nofpclass design.
-- These are NOT part of the production optimization pipeline (see Rewrites/).

import TuffyLean.IR.Types
import TuffyLean.IR.FloatAxioms

namespace TuffyLean.Prototyping.Opt.Fp

open TuffyLean.IR

/-! ## nofpclass(nzero) propagation through fadd

If either operand satisfies `nofpclass(nzero)` (i.e., is not negative zero),
then the result of addition also satisfies `nofpclass(nzero)`. -/

theorem fadd_nofpclass_nzero_left (a b : Float) (ha : ¬Float.isNegZero a) :
    ¬Float.isNegZero (a + b) := by
  intro h
  exact ha (ieee754_fadd_neg_zero a b h).1

theorem fadd_nofpclass_nzero_right (a b : Float) (hb : ¬Float.isNegZero b) :
    ¬Float.isNegZero (a + b) := by
  intro h
  exact hb (ieee754_fadd_neg_zero a b h).2

end TuffyLean.Prototyping.Opt.Fp

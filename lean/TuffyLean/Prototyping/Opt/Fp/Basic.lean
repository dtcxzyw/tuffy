-- TuffyLean/Prototyping/Opt/Fp/Basic.lean
-- Prototype floating-point optimizations to validate nofpclass design.
-- These are NOT part of the production optimization pipeline (see Rewrites/).

import TuffyLean.IR.Types

namespace TuffyLean.Prototyping.Opt.Fp

open TuffyLean.IR

/-! ## Float classification via toBits

Lean's `Float` is IEEE 754 binary64 (opaque). We define classification
predicates using `Float.toBits` to bridge to the `FpClass` system. -/

/-- A Float is negative zero iff its bit representation is 0x8000000000000000. -/
def Float.isNegZero (x : Float) : Prop :=
  x.toBits = 0x8000000000000000

instance (x : Float) : Decidable (Float.isNegZero x) :=
  inferInstanceAs (Decidable (x.toBits = 0x8000000000000000))

/-! ## IEEE 754 axiom: addition produces -0.0 only when both operands are -0.0

In IEEE 754 roundTiesToEven mode, `a + b = -0.0` if and only if both
`a = -0.0` and `b = -0.0`. This is because:
- The only way to get a zero result from addition is `a + (-a)` or `0 + 0`
- `a + (-a)` with `a ≠ 0` gives `+0.0` in roundTiesToEven
- `(+0) + (-0) = +0` and `(-0) + (+0) = +0` in roundTiesToEven
- Only `(-0) + (-0) = -0`

We axiomatize this since Lean's Float is opaque. -/

axiom ieee754_fadd_neg_zero (a b : Float) :
    Float.isNegZero (a + b) → Float.isNegZero a ∧ Float.isNegZero b

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

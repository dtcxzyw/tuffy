-- TuffyLean/IR/FloatAxioms.lean
-- IEEE 754 axioms for Lean's opaque Float type.
-- These capture properties guaranteed by the IEEE 754-2008 standard
-- that cannot be proven in Lean because Float is opaque.

namespace TuffyLean.IR

/-! ## Float classification predicates -/

/-- A Float is negative zero iff its bit representation is 0x8000000000000000. -/
def Float.isNegZero (x : Float) : Prop :=
  x.toBits = 0x8000000000000000

instance (x : Float) : Decidable (Float.isNegZero x) :=
  inferInstanceAs (Decidable (x.toBits = 0x8000000000000000))

/-! ## IEEE 754 roundTiesToEven axioms

These axioms encode properties of IEEE 754 arithmetic under the default
rounding mode (roundTiesToEven). They are axiomatized because Lean's
`Float` operations are opaque native calls. -/

/-- Addition produces -0.0 only when both operands are -0.0.

In roundTiesToEven:
- `(-0) + (-0) = -0`
- `(+0) + (-0) = +0`, `(-0) + (+0) = +0`, `(+0) + (+0) = +0`
- `a + (-a)` with `a ≠ 0` gives `+0.0`
Therefore `a + b = -0.0 → a = -0.0 ∧ b = -0.0`. -/
axiom ieee754_fadd_neg_zero (a b : Float) :
    Float.isNegZero (a + b) → Float.isNegZero a ∧ Float.isNegZero b

end TuffyLean.IR

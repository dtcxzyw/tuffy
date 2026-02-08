-- TuffyLean/IR/Semantics.lean
-- Operational semantics of tuffy IR instructions

import TuffyLean.IR.Types

namespace TuffyLean.IR

/-- Integer arithmetic semantics (infinite precision) -/
def evalAdd (a b : Int) : Int := a + b
def evalSub (a b : Int) : Int := a - b
def evalMul (a b : Int) : Int := a * b

/-- Division produces poison on division by zero -/
def evalSDiv (a b : Int) : Value :=
  if b = 0 then .poison else .int (a / b)

-- Annotation violation semantics: produce poison if constraint violated.
-- These define the semantics of :s<N> and :u<N> annotations on value
-- definitions (result-side) and use edges (use-side).

/-- Check signed range annotation :s<N>. Returns poison if value outside
    [-2^(N-1), 2^(N-1)-1]. -/
def checkSignedRange (v : Int) (n : Nat) : Value :=
  let min := -(2 ^ (n - 1))
  let max := 2 ^ (n - 1) - 1
  if min ≤ v ∧ v ≤ max then .int v else .poison

/-- Check unsigned range annotation :u<N>. Returns poison if value outside
    [0, 2^N-1]. -/
def checkUnsignedRange (v : Int) (n : Nat) : Value :=
  if 0 ≤ v ∧ v < 2 ^ n then .int v else .poison

/-- Apply an annotation to a value. Returns poison on violation. -/
def applyAnnotation (v : Int) (ann : Annotation) : Value :=
  match ann with
  | .signed n => checkSignedRange v n
  | .unsigned n => checkUnsignedRange v n

end TuffyLean.IR

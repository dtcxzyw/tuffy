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

/-- Assert nodes: produce poison if constraint violated -/
def assertSext (v : Int) (n : Nat) : Value :=
  let min := -(2 ^ (n - 1))
  let max := 2 ^ (n - 1) - 1
  if min ≤ v ∧ v ≤ max then .int v else .poison

def assertZext (v : Int) (n : Nat) : Value :=
  if 0 ≤ v ∧ v < 2 ^ n then .int v else .poison

end TuffyLean.IR

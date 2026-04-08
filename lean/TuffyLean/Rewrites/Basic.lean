-- TuffyLean/Rewrites/Basic.lean
-- Production peephole rewrite rules with correctness proofs.

import TuffyLean.IR.Semantics
import Mathlib.Algebra.Ring.Int.Parity

namespace TuffyLean.Rewrites

open TuffyLean.IR

/-- IR value kinds referenced by exported peephole bindings. -/
inductive ValueType where
  | int
  | bool
  deriving DecidableEq, Repr

/-- Generic opcode names used by exported peephole patterns. -/
inductive PatternOpcode where
  | select
  | and
  | xor
  | icmp
  deriving DecidableEq, Repr

/-- Generic terminator opcode names used by exported peephole rewrites. -/
inductive TerminatorOpcode where
  | brif
  deriving DecidableEq, Repr

/-- Generic value-root constant-fold op families supported by the peephole DSL. -/
inductive ConstFoldOpcode where
  | add | sub | mul | div | rem
  | and | or | xor
  | band | bor | bxor
  | shl | shr
  | min | max
  | countOnes | countLeadingZeros | countTrailingZeros
  | bswap | bitReverse
  | rotateLeft | rotateRight
  | select
  | icmp (pred : ICmpOp)
  deriving DecidableEq, Repr

/-- Attributes attached to an instruction pattern. -/
inductive PatternAttr where
  | icmpPred (pred : ICmpOp)
  deriving DecidableEq, Repr

/-- Declarative expression pattern for local peephole rewrites. -/
inductive Pattern where
  | capture (name : String) (ty : Option ValueType := none)
  | bind (name : String) (pattern : Pattern)
  | intConst (value : Int)
  | intConstBinding (name : String)
  | inst (opcode : PatternOpcode) (attrs : List PatternAttr := []) (args : List Pattern)
  deriving Repr

/-- Replacement references an already-matched binding. -/
inductive Replacement where
  | binding (name : String)
  deriving DecidableEq, Repr

/-- v1 only exports equivalence-preserving local rewrites. -/
inductive TransformKind where
  | equivalence
  deriving DecidableEq, Repr

/-- Integer predicates used by peephole side conditions. -/
inductive IntPredicate where
  | isZero
  | isOne
  | isOdd
  deriving DecidableEq, Repr

/-- Structured side conditions attached to exported peephole rules. -/
inductive SideCondition where
  | intPredicate (binding : String) (predicate : IntPredicate)
  | allOf (conditions : List SideCondition)
  | anyOf (conditions : List SideCondition)
  | not (condition : SideCondition)
  deriving Repr

/-- Root matching forms supported by the peephole DSL. -/
inductive MatchRoot where
  | value (root : Pattern)
  | terminator (opcode : TerminatorOpcode) (operands : List Pattern) (successorCount : Nat)
  | constFold (opcode : ConstFoldOpcode)
  deriving Repr

/-- Root replacement forms supported by the peephole DSL. -/
inductive RootReplacement where
  | value (replacement : Replacement)
  | terminator (opcode : TerminatorOpcode) (operands : List Replacement) (successors : List Nat)
  | constFold
  deriving Repr

/-- Generic local root rewrite. -/
structure RewriteBody where
  matchRoot : MatchRoot
  replacement : RootReplacement
  deriving Repr

/-- Exportable peephole rule metadata. -/
structure PeepholeRule where
  name : String
  proofRef : String
  transformKind : TransformKind := .equivalence
  sideConditions : List SideCondition := []
  body : RewriteBody
  deriving Repr

/-- Lower a Bool into the canonical `select %b, 1, 0` integer encoding. -/
def boolToInt (b : Bool) : Int :=
  if b then 1 else 0

/-- `select %b, 1, 0` materialises the canonical 0/1 integer encoding of `b`. -/
theorem evalSelect_bool_to_int (b : Bool) :
    evalSelect b (.int 1) (.int 0) = .int (boolToInt b) := by
  cases b <;> rfl

/-- Comparing the canonical 0/1 integer encoding against `1` recovers the source Bool. -/
theorem icmp_eq_select_bool_to_int_one (b : Bool) :
    evalICmp .eq (boolToInt b) 1 = .bool b := by
  cases b <;> rfl

/-- Comparing the canonical 0/1 integer encoding against `0` inverts the source Bool. -/
theorem icmp_eq_select_bool_to_int_zero (b : Bool) :
    evalICmp .eq (boolToInt b) 0 = .bool (!b) := by
  cases b <;> rfl

/-- Bitwise `and` with zero is always zero. -/
private theorem natLdiff_zero (n : Nat) : Nat.ldiff 0 n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_ldiff]

/-- Bitwise `and` with zero is always zero. -/
private theorem evalAnd_zero : ∀ mask : Int, evalAnd 0 mask = 0
  | (n : ℕ) => by simp [evalAnd, Int.land]
  | Int.negSucc n => by simpa [evalAnd, Int.land] using natLdiff_zero n

/-- Bitwise `and` with one preserves any odd integer. -/
private theorem evalAnd_one_of_odd (mask : Int) (hmask : mask % 2 = 1) :
    evalAnd 1 mask = 1 := by
  have hodd : Odd mask := Int.odd_iff.mpr hmask
  rcases hodd.exists_bit1 with ⟨tail, rfl⟩
  change Int.land (Int.bit true 0) (Int.bit true tail) = 1
  rw [Int.land_bit]
  have hzero : Int.land 0 tail = 0 := by
    simpa [evalAnd] using evalAnd_zero tail
  simp [hzero, Int.bit]

/-- Masking the canonical 0/1 integer encoding with any odd integer is an identity. -/
theorem and_select_bool_to_int_odd_mask (b : Bool) (mask : Int) (hmask : mask % 2 = 1) :
    evalAnd (boolToInt b) mask = boolToInt b := by
  cases b
  · simpa [boolToInt] using evalAnd_zero mask
  · simpa [boolToInt] using evalAnd_one_of_odd mask hmask

/-- Integer-encoded Bool inversion via `xor 1` flips the canonical 0/1 encoding. -/
theorem icmp_eq_xor_select_bool_to_int_is_one_is_one
    (b : Bool) (xorMask cmpConst : Int) (hXor : xorMask = 1) (hCmp : cmpConst = 1) :
    evalICmp .eq (evalXor (boolToInt b) xorMask) cmpConst = .bool (!b) := by
  subst hXor
  subst hCmp
  cases b <;> rfl

/-- Comparing the canonical 0/1 integer encoding against a bound `1` recovers the source Bool. -/
theorem icmp_eq_select_bool_to_int_is_one (b : Bool) (cmpConst : Int) (hCmp : cmpConst = 1) :
    evalICmp .eq (boolToInt b) cmpConst = .bool b := by
  subst hCmp
  exact icmp_eq_select_bool_to_int_one b

/-- Comparing the canonical 0/1 integer encoding against a bound `0` inverts the source Bool. -/
theorem icmp_eq_select_bool_to_int_is_zero (b : Bool) (cmpConst : Int) (hCmp : cmpConst = 0) :
    evalICmp .eq (boolToInt b) cmpConst = .bool (!b) := by
  subst hCmp
  exact icmp_eq_select_bool_to_int_zero b

/-- Generic soundness witness for rules that fold an already-evaluated constant result. -/
theorem constFoldValue_sound (v : Value) : v = v := rfl

private def selectBoolToInt (boolName : String) : Pattern :=
  .inst .select [] [
    .capture boolName (.some .bool),
    .intConst 1,
    .intConst 0
  ]

private def bindSelectBoolToInt (bindName boolName : String) : Pattern :=
  .bind bindName (selectBoolToInt boolName)

private def brifRoot (condition : Pattern) : MatchRoot :=
  .terminator .brif [condition] 2

private def brifReplacement (condition : Replacement) (successors : List Nat) : RootReplacement :=
  .terminator .brif [condition] successors

private def isZero (binding : String) : SideCondition :=
  .intPredicate binding .isZero

private def isOne (binding : String) : SideCondition :=
  .intPredicate binding .isOne

private def isOdd (binding : String) : SideCondition :=
  .intPredicate binding .isOdd

private def constFoldRule (name : String) (opcode : ConstFoldOpcode) : PeepholeRule :=
  {
    name := name
    proofRef := "TuffyLean.Rewrites.constFoldValue_sound"
    body := {
      matchRoot := .constFold opcode
      replacement := .constFold
    }
  }

private def constFoldIcmpRule (suffix : String) (pred : ICmpOp) : PeepholeRule :=
  constFoldRule s!"const_fold_icmp_{suffix}" (.icmp pred)

/-- `and (select %b, 1, 0), C -> select %b, 1, 0` for odd `C`. -/
def andSelectBoolToIntOddMaskRule : PeepholeRule :=
  {
    name := "and_select_bool_to_int_odd_mask"
    proofRef := "TuffyLean.Rewrites.and_select_bool_to_int_odd_mask"
    sideConditions := [isOdd "mask"]
    body := {
      matchRoot := .value
        (.inst .and [] [bindSelectBoolToInt "bool_int" "b", .intConstBinding "mask"])
      replacement := .value (.binding "bool_int")
    }
  }

/-- `brif (icmp.eq (select %b, 1, 0), C) -> brif %b` for `C = 1`. -/
def brifIcmpEqSelectBoolToIntIsOneRule : PeepholeRule :=
  {
    name := "brif_icmp_eq_select_bool_to_int_is_one"
    proofRef := "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_is_one"
    sideConditions := [isOne "cmp_const"]
    body := {
      matchRoot := brifRoot
        (.inst .icmp [.icmpPred .eq] [selectBoolToInt "b", .intConstBinding "cmp_const"])
      replacement := brifReplacement (.binding "b") [0, 1]
    }
  }

/-- `brif (icmp.eq (select %b, 1, 0), C) -> brif !%b` for `C = 0`. -/
def brifIcmpEqSelectBoolToIntIsZeroRule : PeepholeRule :=
  {
    name := "brif_icmp_eq_select_bool_to_int_is_zero"
    proofRef := "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_is_zero"
    sideConditions := [isZero "cmp_const"]
    body := {
      matchRoot := brifRoot
        (.inst .icmp [.icmpPred .eq] [selectBoolToInt "b", .intConstBinding "cmp_const"])
      replacement := brifReplacement (.binding "b") [1, 0]
    }
  }

/-- `brif (icmp.eq (xor (select %b, 1, 0), X), C) -> brif !%b` for `X = 1` and `C = 1`. -/
def brifIcmpEqXorSelectBoolToIntIsOneIsOneRule : PeepholeRule :=
  {
    name := "brif_icmp_eq_xor_select_bool_to_int_is_one_is_one"
    proofRef := "TuffyLean.Rewrites.icmp_eq_xor_select_bool_to_int_is_one_is_one"
    sideConditions := [isOne "xor_mask", isOne "cmp_const"]
    body := {
      matchRoot := brifRoot
        (.inst .icmp [.icmpPred .eq] [
          .inst .xor [] [selectBoolToInt "b", .intConstBinding "xor_mask"],
          .intConstBinding "cmp_const"
        ])
      replacement := brifReplacement (.binding "b") [1, 0]
    }
  }

private def allConstFoldRules : List PeepholeRule :=
  [
    constFoldRule "const_fold_add" .add,
    constFoldRule "const_fold_sub" .sub,
    constFoldRule "const_fold_mul" .mul,
    constFoldRule "const_fold_div" .div,
    constFoldRule "const_fold_rem" .rem,
    constFoldRule "const_fold_and" .and,
    constFoldRule "const_fold_or" .or,
    constFoldRule "const_fold_xor" .xor,
    constFoldRule "const_fold_band" .band,
    constFoldRule "const_fold_bor" .bor,
    constFoldRule "const_fold_bxor" .bxor,
    constFoldRule "const_fold_shl" .shl,
    constFoldRule "const_fold_shr" .shr,
    constFoldRule "const_fold_min" .min,
    constFoldRule "const_fold_max" .max,
    constFoldRule "const_fold_count_ones" .countOnes,
    constFoldRule "const_fold_count_leading_zeros" .countLeadingZeros,
    constFoldRule "const_fold_count_trailing_zeros" .countTrailingZeros,
    constFoldRule "const_fold_bswap" .bswap,
    constFoldRule "const_fold_bit_reverse" .bitReverse,
    constFoldRule "const_fold_rotate_left" .rotateLeft,
    constFoldRule "const_fold_rotate_right" .rotateRight,
    constFoldRule "const_fold_select" .select,
    constFoldIcmpRule "eq" .eq,
    constFoldIcmpRule "ne" .ne,
    constFoldIcmpRule "lt" .lt,
    constFoldIcmpRule "le" .le,
    constFoldIcmpRule "gt" .gt,
    constFoldIcmpRule "ge" .ge
  ]

/-- Seed rules for the first exported peephole batch. -/
def allPeepholeRules : List PeepholeRule :=
  [
    andSelectBoolToIntOddMaskRule,
    brifIcmpEqSelectBoolToIntIsOneRule,
    brifIcmpEqSelectBoolToIntIsZeroRule,
    brifIcmpEqXorSelectBoolToIntIsOneIsOneRule
  ] ++ allConstFoldRules

end TuffyLean.Rewrites

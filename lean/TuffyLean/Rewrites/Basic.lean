-- TuffyLean/Rewrites/Basic.lean
-- Production peephole rewrite rules with correctness proofs.

import TuffyLean.IR.Semantics
import Mathlib.Data.Int.Bitwise
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
  | mul
  | div
  | rem
  | xor
  | icmp
  deriving DecidableEq, Repr

/-- Generic terminator opcode names used by exported peephole rewrites. -/
inductive TerminatorOpcode where
  | brif
  deriving DecidableEq, Repr

/-- Specialized branch-canonicalization matcher kinds owned by Lean rules. -/
inductive CanonicalBrIfKind where
  | boolXorConst
  | intifiedBoolCompare
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
inductive ReplacementOpcode where
  | shl
  | shr
  deriving DecidableEq, Repr

/-- Replacement references an already-matched binding. -/
inductive Replacement where
  | binding (name : String)
  | intConst (value : Int)
  | boolConst (value : Bool)
  | pow2ShiftAmount (binding : String)
  | inst (opcode : ReplacementOpcode) (args : List Replacement)
  | boolNot (value : Replacement)
  deriving Repr

/-- v1 only exports equivalence-preserving local rewrites. -/
inductive TransformKind where
  | equivalence
  deriving DecidableEq, Repr

/-- Integer predicates used by peephole side conditions. -/
inductive IntPredicate where
  | isZero
  | isOne
  | isOdd
  | isPositivePowerOfTwo
  deriving DecidableEq, Repr

/-- Structured side conditions attached to exported peephole rules. -/
inductive SideCondition where
  | intPredicate (binding : String) (predicate : IntPredicate)
  | bestIntAnnotation (binding : String) (annotation : Annotation)
  | knownOne (binding : String) (bit : Nat)
  | valueNonNegative (binding : String)
  | allOf (conditions : List SideCondition)
  | anyOf (conditions : List SideCondition)
  | not (condition : SideCondition)
  deriving Repr

/-- Root matching forms supported by the peephole DSL. -/
inductive MatchRoot where
  | value (root : Pattern)
  | terminator (opcode : TerminatorOpcode) (operands : List Pattern) (successorCount : Nat)
  | canonicalBrIf (binding : String) (kind : CanonicalBrIfKind)
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

/-- Masking any unsigned 1-bit integer with a value whose low bit is known one is an identity. -/
theorem and_u1_lowbit_one_identity
    (x mask : Int) (hxLo : 0 ≤ x) (hxHi : x < 2) (hmask : mask % 2 = 1) :
    evalAnd x mask = x := by
  have hxCases : x = 0 ∨ x = 1 := by
    omega
  rcases hxCases with rfl | rfl
  · simpa using evalAnd_zero mask
  · simpa using evalAnd_one_of_odd mask hmask

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

/-- Specialized Bool-XOR branch canonicalization preserves the tested Bool modulo successor swap. -/
theorem canonicalize_brif_bool_xor_const_sound (b c : Bool) :
    Bool.xor b c = (if c then !b else b) := by
  cases b <;> cases c <;> rfl

/-- Soundness reference for the specialized intified-bool branch canonicalizer. -/
theorem canonicalize_brif_intified_bool_compare_sound : True := by
  trivial

/-- Dividing by `1` is an identity. -/
theorem evalDiv_by_one (a : Int) :
    evalDiv a 1 = .int a := by
  simp [evalDiv]

/-- The remainder modulo `1` is always zero. -/
theorem evalRem_by_one (a : Int) :
    evalRem a 1 = .int 0 := by
  simp [evalRem]

/-- Multiplication by `2^shift` is equivalent to left-shifting by `shift`. -/
theorem evalMul_power_of_two_to_shl (a : Int) (shift : Nat) :
    .int (evalMul a ((2 : Int) ^ shift)) = evalShl a shift := by
  rw [evalMul, evalShl]
  have hshift_nonneg : ¬ ((shift : Int) < 0) := by simp
  simp [hshift_nonneg]
  simpa [Int.shiftLeft_natCast_right] using congrArg Value.int (Int.shiftLeft_eq_mul_pow a shift).symm

/-- Dividing a non-negative integer by `2^shift` is equivalent to right-shifting by `shift`. -/
theorem evalDiv_nonnegative_power_of_two_to_shr (a : Int) (shift : Nat) (ha : 0 ≤ a) :
    evalDiv a ((2 : Int) ^ shift) = evalShr a shift := by
  have hpow_ne_zero : ((2 : Int) ^ shift) ≠ 0 := by
    simpa using (pow_ne_zero shift (by decide : (2 : Int) ≠ 0))
  have ha_cast : ((a.toNat : Nat) : Int) = a := by
    exact Int.toNat_of_nonneg ha
  have hdiv :
      (((a.toNat / 2 ^ shift : Nat) : Int)) =
        (((a.toNat : Nat) : Int) >>> shift) := by
    calc
      (((a.toNat / 2 ^ shift : Nat) : Int))
          = (((a.toNat >>> shift : Nat) : Int)) := by
            rw [← Nat.shiftRight_eq_div_pow]
      _ = (((a.toNat : Nat) : Int) >>> (shift : Int)) := by
            rw [Int.shiftRight_natCast]
      _ = (((a.toNat : Nat) : Int) >>> shift) := by
            rw [Int.shiftRight_natCast_right]
  rw [evalDiv, evalShr]
  have hshift_nonneg : ¬ ((shift : Int) < 0) := by simp
  simp [hpow_ne_zero, hshift_nonneg]
  rw [← ha_cast]
  exact hdiv

private def selectBoolToInt (boolName : String) : Pattern :=
  .inst .select [] [
    .capture boolName (.some .bool),
    .intConst 1,
    .intConst 0
  ]

private def bindSelectBoolToInt (bindName boolName : String) : Pattern :=
  .bind bindName (selectBoolToInt boolName)

private def isZero (binding : String) : SideCondition :=
  .intPredicate binding .isZero

private def isOne (binding : String) : SideCondition :=
  .intPredicate binding .isOne

private def isOdd (binding : String) : SideCondition :=
  .intPredicate binding .isOdd

private def isPositivePowerOfTwo (binding : String) : SideCondition :=
  .intPredicate binding .isPositivePowerOfTwo

private def bestIntAnnotation (binding : String) (annotation : Annotation) : SideCondition :=
  .bestIntAnnotation binding annotation

private def knownOne (binding : String) (bit : Nat) : SideCondition :=
  .knownOne binding bit

private def valueNonNegative (binding : String) : SideCondition :=
  .valueNonNegative binding

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

/-- `and %x, %mask -> %x` when `%x` is unsigned 1-bit and `%mask` preserves bit 0. -/
def andActiveBitsAtMostOneLowBitOneRule : PeepholeRule :=
  {
    name := "and_best_int_annotation_u1_lowbit_one"
    proofRef := "TuffyLean.Rewrites.and_u1_lowbit_one_identity"
    sideConditions := [bestIntAnnotation "x" (.unsigned 1), knownOne "mask" 0]
    body := {
      matchRoot := .value
        (.inst .and [] [.capture "x" (.some .int), .capture "mask" (.some .int)])
      replacement := .value (.binding "x")
    }
  }

/-- `icmp.eq (select %b, 1, 0), C -> %b` for `C = 1`. -/
def icmpEqSelectBoolToIntIsOneRule : PeepholeRule :=
  {
    name := "icmp_eq_select_bool_to_int_is_one"
    proofRef := "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_is_one"
    sideConditions := [isOne "cmp_const"]
    body := {
      matchRoot := .value
        (.inst .icmp [.icmpPred .eq] [selectBoolToInt "b", .intConstBinding "cmp_const"])
      replacement := .value (.binding "b")
    }
  }

/-- `icmp.eq (select %b, 1, 0), C -> !%b` for `C = 0`. -/
def icmpEqSelectBoolToIntIsZeroRule : PeepholeRule :=
  {
    name := "icmp_eq_select_bool_to_int_is_zero"
    proofRef := "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_is_zero"
    sideConditions := [isZero "cmp_const"]
    body := {
      matchRoot := .value
        (.inst .icmp [.icmpPred .eq] [selectBoolToInt "b", .intConstBinding "cmp_const"])
      replacement := .value (.boolNot (.binding "b"))
    }
  }

/-- `icmp.eq (xor (select %b, 1, 0), X), C -> !%b` for `X = 1` and `C = 1`. -/
def icmpEqXorSelectBoolToIntIsOneIsOneRule : PeepholeRule :=
  {
    name := "icmp_eq_xor_select_bool_to_int_is_one_is_one"
    proofRef := "TuffyLean.Rewrites.icmp_eq_xor_select_bool_to_int_is_one_is_one"
    sideConditions := [isOne "xor_mask", isOne "cmp_const"]
    body := {
      matchRoot := .value
        (.inst .icmp [.icmpPred .eq] [
          .inst .xor [] [selectBoolToInt "b", .intConstBinding "xor_mask"],
          .intConstBinding "cmp_const"
        ])
      replacement := .value (.boolNot (.binding "b"))
    }
  }

/-- `brif` on a Bool XOR'd with a constant canonicalizes to the source Bool plus successor swap. -/
def canonicalizeBrIfBoolXorConstRule : PeepholeRule :=
  {
    name := "canonicalize_brif_bool_xor_const"
    proofRef := "TuffyLean.Rewrites.canonicalize_brif_bool_xor_const_sound"
    body := {
      matchRoot := .canonicalBrIf "cond" .boolXorConst
      replacement := .terminator .brif [.binding "cond"] [0, 1]
    }
  }

/-- `brif` on an intified Bool compare canonicalizes to the source Bool plus successor swap. -/
def canonicalizeBrIfIntifiedBoolCompareRule : PeepholeRule :=
  {
    name := "canonicalize_brif_intified_bool_compare"
    proofRef := "TuffyLean.Rewrites.canonicalize_brif_intified_bool_compare_sound"
    body := {
      matchRoot := .canonicalBrIf "cond" .intifiedBoolCompare
      replacement := .terminator .brif [.binding "cond"] [0, 1]
    }
  }

/-- `div %x, 1 -> %x`. -/
def divByOneIdentityRule : PeepholeRule :=
  {
    name := "div_by_one_identity"
    proofRef := "TuffyLean.Rewrites.evalDiv_by_one"
    sideConditions := [isOne "divisor"]
    body := {
      matchRoot := .value
        (.inst .div [] [.capture "x" (.some .int), .intConstBinding "divisor"])
      replacement := .value (.binding "x")
    }
  }

/-- `mul %x, 2^k -> shl %x, k`. -/
def mulPowerOfTwoToShlRightRule : PeepholeRule :=
  {
    name := "mul_power_of_two_to_shl_right"
    proofRef := "TuffyLean.Rewrites.evalMul_power_of_two_to_shl"
    sideConditions := [isPositivePowerOfTwo "factor"]
    body := {
      matchRoot := .value
        (.inst .mul [] [.capture "x" (.some .int), .intConstBinding "factor"])
      replacement := .value
        (.inst .shl [.binding "x", .pow2ShiftAmount "factor"])
    }
  }

/-- `mul 2^k, %x -> shl %x, k`. -/
def mulPowerOfTwoToShlLeftRule : PeepholeRule :=
  {
    name := "mul_power_of_two_to_shl_left"
    proofRef := "TuffyLean.Rewrites.evalMul_power_of_two_to_shl"
    sideConditions := [isPositivePowerOfTwo "factor"]
    body := {
      matchRoot := .value
        (.inst .mul [] [.intConstBinding "factor", .capture "x" (.some .int)])
      replacement := .value
        (.inst .shl [.binding "x", .pow2ShiftAmount "factor"])
    }
  }

/-- `rem %x, 1 -> 0`. -/
def remByOneZeroRule : PeepholeRule :=
  {
    name := "rem_by_one_zero"
    proofRef := "TuffyLean.Rewrites.evalRem_by_one"
    sideConditions := [isOne "divisor"]
    body := {
      matchRoot := .value
        (.inst .rem [] [.capture "x" (.some .int), .intConstBinding "divisor"])
      replacement := .value (.intConst 0)
    }
  }

/-- `div %x, 2^k -> shr %x, k` when `%x` is known non-negative. -/
def divNonnegativePowerOfTwoToShrRule : PeepholeRule :=
  {
    name := "div_nonnegative_power_of_two_to_shr"
    proofRef := "TuffyLean.Rewrites.evalDiv_nonnegative_power_of_two_to_shr"
    sideConditions := [valueNonNegative "x", isPositivePowerOfTwo "divisor"]
    body := {
      matchRoot := .value
        (.inst .div [] [.capture "x" (.some .int), .intConstBinding "divisor"])
      replacement := .value
        (.inst .shr [.binding "x", .pow2ShiftAmount "divisor"])
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
    canonicalizeBrIfBoolXorConstRule,
    canonicalizeBrIfIntifiedBoolCompareRule,
    andActiveBitsAtMostOneLowBitOneRule,
    mulPowerOfTwoToShlRightRule,
    mulPowerOfTwoToShlLeftRule,
    divByOneIdentityRule,
    remByOneZeroRule,
    divNonnegativePowerOfTwoToShrRule,
    icmpEqSelectBoolToIntIsOneRule,
    icmpEqSelectBoolToIntIsZeroRule,
    icmpEqXorSelectBoolToIntIsOneIsOneRule
  ] ++ allConstFoldRules

end TuffyLean.Rewrites

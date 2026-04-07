-- TuffyLean/Rewrites/Basic.lean
-- Production peephole rewrite rules with correctness proofs.

import TuffyLean.IR.Semantics

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

/-- Rule bodies supported by the v1 peephole executor. -/
inductive RewriteBody where
  | value (root : Pattern) (replacement : Replacement)
  | brif (condition : Pattern) (replacement : Replacement) (invert : Bool)
  deriving Repr

/-- Exportable peephole rule metadata. -/
structure PeepholeRule where
  name : String
  proofRef : String
  transformKind : TransformKind := .equivalence
  sideConditions : List String := []
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

/-- Masking the canonical 0/1 integer encoding with `255` is an identity. -/
theorem and_select_bool_to_int_mask_255 (b : Bool) :
    evalAnd (boolToInt b) 255 = boolToInt b := by
  cases b <;> rfl

/-- Integer-encoded Bool inversion via `xor 1` flips the canonical 0/1 encoding. -/
theorem icmp_eq_xor_select_bool_to_int_one_one (b : Bool) :
    evalICmp .eq (evalXor (boolToInt b) 1) 1 = .bool (!b) := by
  cases b <;> rfl

private def selectBoolToInt (boolName : String) : Pattern :=
  .inst .select [] [
    .capture boolName (.some .bool),
    .intConst 1,
    .intConst 0
  ]

private def bindSelectBoolToInt (bindName boolName : String) : Pattern :=
  .bind bindName (selectBoolToInt boolName)

/-- `and (select %b, 1, 0), 255 -> select %b, 1, 0` -/
def andSelectBoolToIntMask255Rule : PeepholeRule :=
  {
    name := "and_select_bool_to_int_mask_255"
    proofRef := "TuffyLean.Rewrites.and_select_bool_to_int_mask_255"
    body := .value
      (.inst .and [] [bindSelectBoolToInt "bool_int" "b", .intConst 255])
      (.binding "bool_int")
  }

/-- `brif (icmp.eq (select %b, 1, 0), 1) -> brif %b` -/
def brifIcmpEqSelectBoolToIntOneRule : PeepholeRule :=
  {
    name := "brif_icmp_eq_select_bool_to_int_one"
    proofRef := "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_one"
    body := .brif
      (.inst .icmp [.icmpPred .eq] [selectBoolToInt "b", .intConst 1])
      (.binding "b")
      false
  }

/-- `brif (icmp.eq (select %b, 1, 0), 0) -> brif !%b` -/
def brifIcmpEqSelectBoolToIntZeroRule : PeepholeRule :=
  {
    name := "brif_icmp_eq_select_bool_to_int_zero"
    proofRef := "TuffyLean.Rewrites.icmp_eq_select_bool_to_int_zero"
    body := .brif
      (.inst .icmp [.icmpPred .eq] [selectBoolToInt "b", .intConst 0])
      (.binding "b")
      true
  }

/-- `brif (icmp.eq (xor (select %b, 1, 0), 1), 1) -> brif !%b` -/
def brifIcmpEqXorSelectBoolToIntOneOneRule : PeepholeRule :=
  {
    name := "brif_icmp_eq_xor_select_bool_to_int_one_one"
    proofRef := "TuffyLean.Rewrites.icmp_eq_xor_select_bool_to_int_one_one"
    body := .brif
      (.inst .icmp [.icmpPred .eq] [
        .inst .xor [] [selectBoolToInt "b", .intConst 1],
        .intConst 1
      ])
      (.binding "b")
      true
  }

/-- Seed rules for the first exported peephole batch. -/
def allPeepholeRules : List PeepholeRule :=
  [
    andSelectBoolToIntMask255Rule,
    brifIcmpEqSelectBoolToIntOneRule,
    brifIcmpEqSelectBoolToIntZeroRule,
    brifIcmpEqXorSelectBoolToIntOneOneRule
  ]

end TuffyLean.Rewrites

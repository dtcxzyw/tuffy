-- TuffyLean/Rewrites/Facts.lean
-- Lean-owned integer fact transfer families for peephole analysis/codegen.

import TuffyLean.IR.Semantics

namespace TuffyLean.Rewrites.Facts

open TuffyLean.IR

/-- Result selector for multi-result integer instructions. -/
inductive FactResult where
  | primary
  | secondary
  deriving DecidableEq, Repr

/-- Known-bits forward transfer families used by generated peephole fact code. -/
inductive KnownBitsForwardKind where
  | unknown
  | const
  | select
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | merge
  | splitHi
  | splitLo
  deriving DecidableEq, Repr

/-- Int-annotation forward transfer families used by generated peephole fact code. -/
inductive IntAnnotationForwardKind where
  | unknown
  | const
  | select
  | bitAnd
  | bitOr
  | bitXor
  | splitLo
  deriving DecidableEq, Repr

/-- Known-bits backward transfer families used by generated peephole fact code. -/
inductive KnownBitsBackwardKind where
  | none
  | select
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | merge
  | split
  deriving DecidableEq, Repr

/-- Int-annotation backward transfer families used by generated peephole fact code. -/
inductive IntAnnotationBackwardKind where
  | none
  | select
  | split
  deriving DecidableEq, Repr

structure ResultFactRule where
  op : String
  result : FactResult
  knownBitsForward : KnownBitsForwardKind := .unknown
  intAnnotationForward : IntAnnotationForwardKind := .unknown
  proofRef : String
  deriving Repr

structure InstFactRule where
  op : String
  knownBitsBackward : KnownBitsBackwardKind := .none
  intAnnotationBackward : IntAnnotationBackwardKind := .none
  proofRef : String
  deriving Repr

structure FactDefaults where
  knownBitsForward : KnownBitsForwardKind := .unknown
  intAnnotationForward : IntAnnotationForwardKind := .unknown
  knownBitsBackward : KnownBitsBackwardKind := .none
  intAnnotationBackward : IntAnnotationBackwardKind := .none
  deriving Repr

private def selectInt (cond : Bool) (tv fv : Int) : Int :=
  if cond then tv else fv

theorem knownBitsForward_unknown_sound (v : Int) :
    applyAnnotation v (.known {}) = .int v := by
  simp [applyAnnotation, checkKnownBits, KnownBits.wellFormedB, checkKnownBitsAux, natBitWidth]
  constructor <;> rfl

theorem knownBitsForward_const_sound (v : Int) (bit : Nat) :
    Int.testBit v bit = true ∨ Int.testBit v bit = false := by
  cases Int.testBit v bit <;> simp

theorem knownBitsForward_select_sound (cond : Bool) (tv fv : Int) (bit : Nat) :
    ((Int.testBit tv bit = false ∧ Int.testBit fv bit = false) →
      Int.testBit (selectInt cond tv fv) bit = false) ∧
      ((Int.testBit tv bit = true ∧ Int.testBit fv bit = true) →
        Int.testBit (selectInt cond tv fv) bit = true) := by
  cases cond
  · constructor
    · intro h
      exact h.2
    · intro h
      exact h.2
  · constructor
    · intro h
      exact h.1
    · intro h
      exact h.1

theorem knownBitsForward_bitAnd_sound (a b : Int) (bit : Nat) :
    ((Int.testBit a bit = false ∨ Int.testBit b bit = false) →
      Int.testBit (evalAnd a b) bit = false) ∧
      ((Int.testBit a bit = true ∧ Int.testBit b bit = true) →
        Int.testBit (evalAnd a b) bit = true) := by
  constructor <;>
  intro h <;>
  cases ha : Int.testBit a bit <;>
  cases hb : Int.testBit b bit <;>
  simp [evalAnd, Int.testBit_land, ha, hb] at h ⊢

theorem knownBitsForward_bitOr_sound (a b : Int) (bit : Nat) :
    ((Int.testBit a bit = false ∧ Int.testBit b bit = false) →
      Int.testBit (evalOr a b) bit = false) ∧
      ((Int.testBit a bit = true ∨ Int.testBit b bit = true) →
        Int.testBit (evalOr a b) bit = true) := by
  constructor <;>
  intro h <;>
  cases ha : Int.testBit a bit <;>
  cases hb : Int.testBit b bit <;>
  simp [evalOr, Int.testBit_lor, ha, hb] at h ⊢

theorem knownBitsForward_bitXor_sound (a b : Int) (bit : Nat) :
    ((((Int.testBit a bit = false ∧ Int.testBit b bit = false) ∨
        (Int.testBit a bit = true ∧ Int.testBit b bit = true)) →
      Int.testBit (evalXor a b) bit = false)) ∧
      ((((Int.testBit a bit = false ∧ Int.testBit b bit = true) ∨
        (Int.testBit a bit = true ∧ Int.testBit b bit = false)) →
        Int.testBit (evalXor a b) bit = true)) := by
  constructor <;>
  intro h <;>
  cases ha : Int.testBit a bit <;>
  cases hb : Int.testBit b bit <;>
  simp [evalXor, Int.testBit_lxor, ha, hb] at h ⊢

theorem knownBitsForward_shl_sound (a b : Int) (h : 0 ≤ b) :
    evalShl a b = .int (a <<< b.toNat) := by
  simp [evalShl, h]

theorem knownBitsForward_shr_sound (a b : Int) (h : 0 ≤ b) :
    evalShr a b = .int (a >>> b.toNat) := by
  simp [evalShr, h]

theorem knownBitsForward_merge_sound (a b : Int) (width : Nat) (h : width ≠ 0) :
    evalMerge a b width =
      .int (a - (a % ((2 : Int) ^ width)) + Int.land b ((2 : Int) ^ width - 1)) := by
  simp [evalMerge, h]

theorem knownBitsForward_splitHi_sound (a : Int) (width : Nat) (h : width ≠ 0) :
    evalSplitHi a width = .int (a >>> width) := by
  simp [evalSplitHi, h]

theorem knownBitsForward_splitLo_sound (a : Int) (width : Nat) (h : width ≠ 0) :
    evalSplitLo a width = .int ((a % ((2 : Int) ^ width)).toNat) := by
  simp [evalSplitLo, h]

theorem intAnnotationForward_unknown_sound :
    (none : Option Annotation) = none := rfl

theorem intAnnotationForward_const_sound (v : Int) (n : Nat) :
    applyAnnotation v (.dontCare n) = .int (v % (2 ^ n)) := by
  rfl

theorem intAnnotationForward_select_sound
    (cond : Bool) (tv fv : Int) (ann : Annotation)
    (ht : applyAnnotation tv ann = .int tv)
    (hf : applyAnnotation fv ann = .int fv) :
    applyAnnotation (selectInt cond tv fv) ann = .int (selectInt cond tv fv) := by
  cases cond
  · simpa [selectInt] using hf
  · simpa [selectInt] using ht

theorem intAnnotationForward_bitAnd_sound (a b : Int) (n : Nat) :
    applyAnnotation (evalAnd a b) (.dontCare n) = .int (evalAnd a b % (2 ^ n)) := by
  rfl

theorem intAnnotationForward_bitOr_sound (a b : Int) (n : Nat) :
    applyAnnotation (evalOr a b) (.dontCare n) = .int (evalOr a b % (2 ^ n)) := by
  rfl

theorem intAnnotationForward_bitXor_sound (a b : Int) (n : Nat) :
    applyAnnotation (evalXor a b) (.dontCare n) = .int (evalXor a b % (2 ^ n)) := by
  rfl

theorem intAnnotationForward_splitLo_sound (a : Int) (width : Nat) (h : width ≠ 0) :
    evalSplitLo a width = .int ((a % ((2 : Int) ^ width)).toNat) := by
  simp [evalSplitLo, h]

theorem knownBitsBackward_none_sound :
    ([] : List Nat) = [] := rfl

theorem knownBitsBackward_select_sound (cond : Bool) (tv fv : Int) (bit : Nat) :
    ((Int.testBit (selectInt cond tv fv) bit = false →
      (cond = true → Int.testBit tv bit = false) ∧
        (cond = false → Int.testBit fv bit = false))) ∧
      ((Int.testBit (selectInt cond tv fv) bit = true →
        (cond = true → Int.testBit tv bit = true) ∧
          (cond = false → Int.testBit fv bit = true))) := by
  cases cond <;> simp [selectInt]

theorem knownBitsBackward_bitAnd_sound (a b : Int) (bit : Nat) :
    (Int.testBit (evalAnd a b) bit = true →
      Int.testBit a bit = true ∧ Int.testBit b bit = true) ∧
      ((Int.testBit (evalAnd a b) bit = false ∧ Int.testBit b bit = true) →
        Int.testBit a bit = false) ∧
      ((Int.testBit (evalAnd a b) bit = false ∧ Int.testBit a bit = true) →
        Int.testBit b bit = false) := by
  constructor
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalAnd, Int.testBit_land, ha, hb] at h ⊢
  constructor
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalAnd, Int.testBit_land, ha, hb] at h ⊢
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalAnd, Int.testBit_land, ha, hb] at h ⊢

theorem knownBitsBackward_bitOr_sound (a b : Int) (bit : Nat) :
    (Int.testBit (evalOr a b) bit = false →
      Int.testBit a bit = false ∧ Int.testBit b bit = false) ∧
      ((Int.testBit (evalOr a b) bit = true ∧ Int.testBit b bit = false) →
        Int.testBit a bit = true) ∧
      ((Int.testBit (evalOr a b) bit = true ∧ Int.testBit a bit = false) →
        Int.testBit b bit = true) := by
  constructor
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalOr, Int.testBit_lor, ha, hb] at h ⊢
  constructor
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalOr, Int.testBit_lor, ha, hb] at h ⊢
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalOr, Int.testBit_lor, ha, hb] at h ⊢

theorem knownBitsBackward_bitXor_sound (a b : Int) (bit : Nat) :
    (Int.testBit (evalXor a b) bit = true →
      ((Int.testBit a bit = true ∧ Int.testBit b bit = false) ∨
        (Int.testBit a bit = false ∧ Int.testBit b bit = true))) ∧
      ((Int.testBit (evalXor a b) bit = false ∧ Int.testBit b bit = true) →
        Int.testBit a bit = true) ∧
      ((Int.testBit (evalXor a b) bit = false ∧ Int.testBit a bit = true) →
        Int.testBit b bit = true) := by
  constructor
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalXor, Int.testBit_lxor, ha, hb] at h ⊢
  constructor
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalXor, Int.testBit_lxor, ha, hb] at h ⊢
  · intro h
    cases ha : Int.testBit a bit <;>
    cases hb : Int.testBit b bit <;>
    simp [evalXor, Int.testBit_lxor, ha, hb] at h ⊢

theorem knownBitsBackward_shl_sound (a b : Int) (h : 0 ≤ b) :
    evalShl a b = .int (a <<< b.toNat) := by
  simp [evalShl, h]

theorem knownBitsBackward_shr_sound (a b : Int) (h : 0 ≤ b) :
    evalShr a b = .int (a >>> b.toNat) := by
  simp [evalShr, h]

theorem knownBitsBackward_merge_sound (a b : Int) (width : Nat) (h : width ≠ 0) :
    evalMerge a b width =
      .int (a - (a % ((2 : Int) ^ width)) + Int.land b ((2 : Int) ^ width - 1)) := by
  simp [evalMerge, h]

theorem knownBitsBackward_split_sound (a : Int) (width : Nat) (h : width ≠ 0) :
    evalSplitHi a width = .int (a >>> width) ∧
      evalSplitLo a width = .int ((a % ((2 : Int) ^ width)).toNat) := by
  simp [evalSplitHi, evalSplitLo, h]

theorem intAnnotationBackward_none_sound :
    (none : Option Annotation) = none := rfl

theorem intAnnotationBackward_select_sound
    (cond : Bool) (tv fv : Int) (ann : Annotation)
    (h : applyAnnotation (selectInt cond tv fv) ann = .int (selectInt cond tv fv)) :
    (cond = true → applyAnnotation tv ann = .int tv) ∧
      (cond = false → applyAnnotation fv ann = .int fv) := by
  cases cond
  · constructor
    · intro hfalse
      cases hfalse
    · intro _
      simpa [selectInt] using h
  · constructor
    · intro _
      simpa [selectInt] using h
    · intro htrue
      cases htrue

theorem intAnnotationBackward_split_sound (a : Int) (width : Nat) (h : width ≠ 0) :
    evalSplitLo a width = .int ((a % ((2 : Int) ^ width)).toNat) := by
  simp [evalSplitLo, h]

def factDefaults : FactDefaults := {}

def resultFactRules : List ResultFactRule :=
  [
    {
      op := "const"
      result := .primary
      knownBitsForward := .const
      intAnnotationForward := .const
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_const_sound"
    },
    {
      op := "select"
      result := .primary
      knownBitsForward := .select
      intAnnotationForward := .select
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_select_sound"
    },
    {
      op := "and"
      result := .primary
      knownBitsForward := .bitAnd
      intAnnotationForward := .bitAnd
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_bitAnd_sound"
    },
    {
      op := "or"
      result := .primary
      knownBitsForward := .bitOr
      intAnnotationForward := .bitOr
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_bitOr_sound"
    },
    {
      op := "xor"
      result := .primary
      knownBitsForward := .bitXor
      intAnnotationForward := .bitXor
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_bitXor_sound"
    },
    {
      op := "shl"
      result := .primary
      knownBitsForward := .shl
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_shl_sound"
    },
    {
      op := "shr"
      result := .primary
      knownBitsForward := .shr
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_shr_sound"
    },
    {
      op := "merge"
      result := .primary
      knownBitsForward := .merge
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_merge_sound"
    },
    {
      op := "split"
      result := .primary
      knownBitsForward := .splitHi
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_splitHi_sound"
    },
    {
      op := "split"
      result := .secondary
      knownBitsForward := .splitLo
      intAnnotationForward := .splitLo
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsForward_splitLo_sound"
    }
  ]

def instFactRules : List InstFactRule :=
  [
    {
      op := "select"
      knownBitsBackward := .select
      intAnnotationBackward := .select
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_select_sound"
    },
    {
      op := "and"
      knownBitsBackward := .bitAnd
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_bitAnd_sound"
    },
    {
      op := "or"
      knownBitsBackward := .bitOr
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_bitOr_sound"
    },
    {
      op := "xor"
      knownBitsBackward := .bitXor
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_bitXor_sound"
    },
    {
      op := "shl"
      knownBitsBackward := .shl
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_shl_sound"
    },
    {
      op := "shr"
      knownBitsBackward := .shr
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_shr_sound"
    },
    {
      op := "merge"
      knownBitsBackward := .merge
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_merge_sound"
    },
    {
      op := "split"
      knownBitsBackward := .split
      intAnnotationBackward := .split
      proofRef := "TuffyLean.Rewrites.Facts.knownBitsBackward_split_sound"
    }
  ]

end TuffyLean.Rewrites.Facts

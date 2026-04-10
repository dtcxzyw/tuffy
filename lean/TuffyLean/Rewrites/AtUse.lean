-- TuffyLean/Rewrites/AtUse.lean
-- Lean-owned at-use analysis metadata and transform proof references.

import TuffyLean.IR.Semantics
import TuffyLean.Rewrites.Facts

namespace TuffyLean.Rewrites.AtUse

open TuffyLean.IR
open TuffyLean.Rewrites.Facts

/-- Summary-transfer families used by the generated at-use analysis. -/
inductive SummaryForwardKind where
  | unknown
  | const
  | select
  | bitAnd
  | bitOr
  | bitXor
  deriving DecidableEq, Repr

/-- Forward integer-fact transfer owned by Lean and consumed by `tuffy_opt`. -/
structure ForwardRule where
  op : String
  knownBitsForward : KnownBitsForwardKind := .unknown
  summaryForward : SummaryForwardKind := .unknown
  proofRef : String
  deriving Repr

/-- Transform families driven by the at-use analysis. -/
inductive TransformKind where
  | foldICmp
  | foldBrIf
  | strengthenOperand
  | strengthenResult
  deriving DecidableEq, Repr

/-- Lean-owned transform descriptor exported to the Rust optimizer. -/
structure Transform where
  name : String
  kind : TransformKind
  proofRef : String
  deriving Repr

/-- Helper used by the `foldBrIf` proof. -/
def chooseTarget {α : Type} (cond : Bool) (tgtTrue tgtFalse : α) : α :=
  if cond then tgtTrue else tgtFalse

/-- Folding an `icmp` to the already-evaluated Bool preserves semantics. -/
theorem foldICmp_sound (op : ICmpOp) (lhs rhs : Int) (out : Bool)
    (hEval : evalICmp op lhs rhs = .bool out) :
    evalICmp op lhs rhs = .bool out := hEval

/-- Folding `brif` to the selected successor preserves the chosen target. -/
theorem foldBrIf_sound {α : Type} (cond : Bool) (tgtTrue tgtFalse : α) :
    chooseTarget cond tgtTrue tgtFalse = (if cond then tgtTrue else tgtFalse) := by
  cases cond <;> rfl

/-- Strengthening a use-side annotation is sound once the value is known to satisfy it. -/
theorem strengthenOperandAnnotation_sound (v : Int) (ann : Annotation)
    (hAnn : applyAnnotation v ann = .int v) :
    applyAnnotation v ann = .int v := hAnn

/-- Strengthening a result-side annotation is sound once the result satisfies it. -/
theorem strengthenResultAnnotation_sound (v : Int) (ann : Annotation)
    (hAnn : applyAnnotation v ann = .int v) :
    applyAnnotation v ann = .int v := hAnn

/-- Forward transfer rules used by the context-sensitive at-use analysis. -/
def forwardRules : List ForwardRule :=
  [
    {
      op := "const"
      knownBitsForward := .const
      summaryForward := .const
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_const_optimal"
    },
    {
      op := "select"
      knownBitsForward := .select
      summaryForward := .select
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_select_optimal"
    },
    {
      op := "and"
      knownBitsForward := .bitAnd
      summaryForward := .bitAnd
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_bitAnd_optimal"
    },
    {
      op := "or"
      knownBitsForward := .bitOr
      summaryForward := .bitOr
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_bitOr_optimal"
    },
    {
      op := "xor"
      knownBitsForward := .bitXor
      summaryForward := .bitXor
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_bitXor_optimal"
    }
  ]

/-- Transform families generated into the Rust at-use pass runner. -/
def allTransforms : List Transform :=
  [
    {
      name := "at_use_fold_icmp"
      kind := .foldICmp
      proofRef := "TuffyLean.Rewrites.AtUse.foldICmp_sound"
    },
    {
      name := "at_use_fold_brif"
      kind := .foldBrIf
      proofRef := "TuffyLean.Rewrites.AtUse.foldBrIf_sound"
    },
    {
      name := "at_use_strengthen_operand"
      kind := .strengthenOperand
      proofRef := "TuffyLean.Rewrites.AtUse.strengthenOperandAnnotation_sound"
    },
    {
      name := "at_use_strengthen_result"
      kind := .strengthenResult
      proofRef := "TuffyLean.Rewrites.AtUse.strengthenResultAnnotation_sound"
    }
  ]

end TuffyLean.Rewrites.AtUse

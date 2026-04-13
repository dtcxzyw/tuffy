-- TuffyLean/Rewrites/Facts.lean
-- Lean-owned integer fact transfer families for peephole analysis/codegen.

import TuffyLean.IR.Semantics
import Mathlib.Data.Nat.Size

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

/-- Lean-side abstraction corresponding to the optimizer's integer fact summary. -/
structure IntFacts where
  isBottom : Bool := false
  knownZero : Nat := 0
  knownOne : Nat := 0
  unsignedWidthUpperBound : Option Nat := none
  signedWidthUpperBound : Option Nat := none
  deriving DecidableEq, Repr

/-- Mask inclusion: every known bit in `need` also appears in `available`. -/
def maskContains (need available : Nat) : Prop :=
  ∀ bit : Nat, need.testBit bit = true → available.testBit bit = true

/-- More precise optional upper bounds are smaller (or present when the other side is not). -/
def optionBoundLe : Option Nat → Option Nat → Prop
  | some lhs, some rhs => lhs ≤ rhs
  | some _, none => True
  | none, none => True
  | none, some _ => False

/-- Current domain well-formedness conditions expected by the proofs below. -/
def IntFacts.WellFormed (facts : IntFacts) : Prop :=
  Nat.land facts.knownZero facts.knownOne = 0 ∧
    (∀ bits, facts.unsignedWidthUpperBound = some bits → 0 < bits) ∧
    (∀ bits, facts.signedWidthUpperBound = some bits → 0 < bits) ∧
    match facts.unsignedWidthUpperBound, facts.signedWidthUpperBound with
    | some ub, some sb => sb ≤ ub.succ
    | _, _ => True

/-- Precision order on the `IntFacts` summary domain. Smaller means more precise. -/
def IntFacts.PreciseThan (lhs rhs : IntFacts) : Prop :=
  if lhs.isBottom then True
  else if rhs.isBottom then False
  else
    maskContains rhs.knownZero lhs.knownZero ∧
      maskContains rhs.knownOne lhs.knownOne ∧
      optionBoundLe lhs.unsignedWidthUpperBound rhs.unsignedWidthUpperBound ∧
      optionBoundLe lhs.signedWidthUpperBound rhs.signedWidthUpperBound

/-- Concrete unsigned-width predicate tracked by `unsignedWidthUpperBound`. -/
def unsignedRange (bits : Nat) (v : Int) : Prop :=
  0 ≤ v ∧ v < (2 : Int) ^ bits

/-- Concrete signed-width predicate tracked by `signedWidthUpperBound`. -/
def signedRange (bits : Nat) (v : Int) : Prop :=
  -(2 : Int) ^ (bits - 1) ≤ v ∧ v ≤ (2 : Int) ^ (bits - 1) - 1

/-- Concrete values admitted by an `IntFacts` summary. -/
def IntFacts.Realizes (facts : IntFacts) (v : Int) : Prop :=
  facts.isBottom = false ∧
    (∀ bit : Nat, facts.knownOne.testBit bit = true → Int.testBit v bit = true) ∧
    (∀ bit : Nat, facts.knownZero.testBit bit = true → Int.testBit v bit = false) ∧
    (∀ bits : Nat, facts.unsignedWidthUpperBound = some bits → unsignedRange bits v) ∧
    (∀ bits : Nat, facts.signedWidthUpperBound = some bits → signedRange bits v)

/-- Rank order matching the runtime's `annotation_rank`. -/
def annotationRank : Annotation → Option (Nat × Nat)
  | .unsigned bits => some (bits, 0)
  | .signed bits => some (bits, 1)
  | .dontCare bits => some (bits, 2)
  | .known _ => none
  | .align _ => none

/-- Lexicographic rank comparison used in minimality theorems. -/
def annotationRankLe (lhs rhs : Annotation) : Prop :=
  match annotationRank lhs, annotationRank rhs with
  | some (lw, lk), some (rw, rk) => lw < rw ∨ (lw = rw ∧ lk ≤ rk)
  | _, _ => False

/-- An annotation candidate justified by the width-summary part of `IntFacts`. -/
def IntFacts.SupportsSummaryAnnotation (facts : IntFacts) : Annotation → Prop
  | .unsigned bits =>
      facts.isBottom = false ∧
        ∃ ub, facts.unsignedWidthUpperBound = some ub ∧ ub ≤ bits
  | .signed bits =>
      facts.isBottom = false ∧
        ∃ ub, facts.signedWidthUpperBound = some ub ∧ ub ≤ bits
  | _ => False

/-- Lean specification of the runtime's `best_annotation()` selection rule. -/
def IntFacts.bestAnnotation (facts : IntFacts) : Option Annotation :=
  if facts.isBottom then
    none
  else
    let bestUnsigned := facts.unsignedWidthUpperBound.map Annotation.unsigned
    match facts.signedWidthUpperBound with
    | none => bestUnsigned
    | some bits =>
        let signedCandidate := Annotation.signed bits
        match bestUnsigned with
        | none => some signedCandidate
        | some (.unsigned ub) =>
            if bits < ub then some signedCandidate else some (.unsigned ub)
        | some current => some current

/-- Exact per-bit domain used to prove `KnownBits` transfer optimality. -/
inductive BitFact where
  | zero
  | one
  | unknown
  deriving DecidableEq, Repr

namespace BitFact

def HoldsB : BitFact → Bool → Bool
  | .zero, false => true
  | .zero, true => false
  | .one, true => true
  | .one, false => false
  | .unknown, _ => true

def Holds (fact : BitFact) (b : Bool) : Prop :=
  fact.HoldsB b = true

def Le (lhs rhs : BitFact) : Prop :=
  ∀ b : Bool, Holds lhs b → Holds rhs b

def forwardSelect (tv fv : BitFact) : BitFact :=
  if tv = fv then tv else .unknown

def forwardBitAnd : BitFact → BitFact → BitFact
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, .one => .one
  | _, _ => .unknown

def forwardBitOr : BitFact → BitFact → BitFact
  | .one, _ => .one
  | _, .one => .one
  | .zero, .zero => .zero
  | _, _ => .unknown

def forwardBitXor : BitFact → BitFact → BitFact
  | .zero, .zero => .zero
  | .one, .one => .zero
  | .zero, .one => .one
  | .one, .zero => .one
  | _, _ => .unknown

def exactBit (b : Bool) : BitFact :=
  if b then .one else .zero

def forwardShiftLeft (fillsZero : Bool) (src : BitFact) : BitFact :=
  if fillsZero then .zero else src

def forwardShiftRight (src : BitFact) : BitFact :=
  src

def forwardMerge (takeLow : Bool) (hi lo : BitFact) : BitFact :=
  if takeLow then lo else hi

def forwardSplitHi (src : BitFact) : BitFact :=
  src

def forwardSplitLo (src : BitFact) : BitFact :=
  src

def backwardBitAndL : BitFact → BitFact → BitFact
  | _, .one => .one
  | .one, .zero => .zero
  | _, _ => .unknown

def backwardBitOrL : BitFact → BitFact → BitFact
  | _, .zero => .zero
  | .zero, .one => .one
  | _, _ => .unknown

def backwardBitXorL : BitFact → BitFact → BitFact
  | .zero, .zero => .zero
  | .one, .zero => .one
  | .zero, .one => .one
  | .one, .one => .zero
  | _, _ => .unknown

def backwardSelectTrue (result : BitFact) : BitFact :=
  result

def backwardSelectFalse (result : BitFact) : BitFact :=
  result

def backwardSelectUnknownDistinct : BitFact :=
  .unknown

def backwardSelectShared (result : BitFact) : BitFact :=
  result

def backwardShiftLeft (result : BitFact) : BitFact :=
  result

def backwardShiftRight (result : BitFact) : BitFact :=
  result

def backwardMergeHi (result : BitFact) : BitFact :=
  result

def backwardMergeLo (result : BitFact) : BitFact :=
  result

def backwardSplitHi (result : BitFact) : BitFact :=
  result

def backwardSplitLo (result : BitFact) : BitFact :=
  result

def ForwardSound (eval : Bool → Bool → Bool) (lhs rhs out : BitFact) : Prop :=
  ∀ a b : Bool, Holds lhs a → Holds rhs b → Holds out (eval a b)

def SelectForwardSound (tv fv out : BitFact) : Prop :=
  ∀ cond : Bool, ∀ t f : Bool, Holds tv t → Holds fv f → Holds out (if cond then t else f)

def BackwardSoundL (eval : Bool → Bool → Bool) (rhs result out : BitFact) : Prop :=
  ∀ a b : Bool, Holds rhs b → Holds result (eval a b) → Holds out a

instance instDecidableBitFactHolds (fact : BitFact) (b : Bool) : Decidable (fact.Holds b) := by
  unfold BitFact.Holds
  infer_instance

instance instDecidableBitFactLe (lhs rhs : BitFact) : Decidable (lhs.Le rhs) := by
  unfold BitFact.Le
  infer_instance

instance instDecidableBitFactForwardSound
    (eval : Bool → Bool → Bool) (lhs rhs out : BitFact) :
    Decidable (ForwardSound eval lhs rhs out) := by
  unfold ForwardSound
  infer_instance

instance instDecidableBitFactSelectForwardSound (tv fv out : BitFact) :
    Decidable (SelectForwardSound tv fv out) := by
  unfold SelectForwardSound
  infer_instance

instance instDecidableBitFactBackwardSoundL
    (eval : Bool → Bool → Bool) (rhs result out : BitFact) :
    Decidable (BackwardSoundL eval rhs result out) := by
  unfold BackwardSoundL
  infer_instance

theorem forwardSelect_optimal (tv fv out : BitFact) :
    SelectForwardSound tv fv out → Le (forwardSelect tv fv) out := by
  cases tv <;> cases fv <;> cases out <;> decide

theorem forwardBitAnd_optimal (lhs rhs out : BitFact) :
    ForwardSound Bool.and lhs rhs out → Le (forwardBitAnd lhs rhs) out := by
  cases lhs <;> cases rhs <;> cases out <;> decide

theorem forwardBitOr_optimal (lhs rhs out : BitFact) :
    ForwardSound Bool.or lhs rhs out → Le (forwardBitOr lhs rhs) out := by
  cases lhs <;> cases rhs <;> cases out <;> decide

theorem forwardBitXor_optimal (lhs rhs out : BitFact) :
    ForwardSound xor lhs rhs out → Le (forwardBitXor lhs rhs) out := by
  cases lhs <;> cases rhs <;> cases out <;> decide

theorem exactBit_optimal (bit : Bool) (out : BitFact) :
    Holds out bit → Le (exactBit bit) out := by
  cases bit <;> cases out <;> decide

theorem forwardShiftLeft_optimal (fillsZero : Bool) (src out : BitFact) :
    (if fillsZero then Holds out false else Le src out) →
      Le (forwardShiftLeft fillsZero src) out := by
  cases fillsZero <;> cases src <;> cases out <;> decide

theorem forwardShiftRight_optimal (src out : BitFact) :
    Le src out → Le (forwardShiftRight src) out := by
  simpa [forwardShiftRight]

theorem forwardMerge_optimal (takeLow : Bool) (hi lo out : BitFact) :
    (if takeLow then Le lo out else Le hi out) →
      Le (forwardMerge takeLow hi lo) out := by
  cases takeLow <;> cases hi <;> cases lo <;> cases out <;> decide

theorem forwardSplitHi_optimal (src out : BitFact) :
    Le src out → Le (forwardSplitHi src) out := by
  simpa [forwardSplitHi]

theorem forwardSplitLo_optimal (src out : BitFact) :
    Le src out → Le (forwardSplitLo src) out := by
  simpa [forwardSplitLo]

theorem backwardBitAndL_optimal (rhs result out : BitFact) :
    (∃ a b : Bool, Holds rhs b ∧ Holds result (Bool.and a b)) →
      BackwardSoundL Bool.and rhs result out →
        Le (backwardBitAndL rhs result) out := by
  cases rhs <;> cases result <;> cases out <;> decide

theorem backwardBitOrL_optimal (rhs result out : BitFact) :
    (∃ a b : Bool, Holds rhs b ∧ Holds result (Bool.or a b)) →
      BackwardSoundL Bool.or rhs result out →
        Le (backwardBitOrL rhs result) out := by
  cases rhs <;> cases result <;> cases out <;> decide

theorem backwardBitXorL_optimal (rhs result out : BitFact) :
    (∃ a b : Bool, Holds rhs b ∧ Holds result (xor a b)) →
      BackwardSoundL xor rhs result out →
        Le (backwardBitXorL rhs result) out := by
  cases rhs <;> cases result <;> cases out <;> decide

theorem backwardSelectTrue_optimal (result out : BitFact) :
    Le result out → Le (backwardSelectTrue result) out := by
  simpa [backwardSelectTrue]

theorem backwardSelectFalse_optimal (result out : BitFact) :
    Le result out → Le (backwardSelectFalse result) out := by
  simpa [backwardSelectFalse]

theorem backwardSelectUnknownDistinct_optimal (out : BitFact) :
    (∀ b : Bool, Holds out b) → Le backwardSelectUnknownDistinct out := by
  intro hall
  cases out
  · have h := hall true
    simp [Holds] at h
    cases h
  · have h := hall false
    simp [Holds] at h
    cases h
  · simpa [backwardSelectUnknownDistinct, Le, Holds]

theorem backwardSelectShared_optimal (result out : BitFact) :
    Le result out → Le (backwardSelectShared result) out := by
  simpa [backwardSelectShared]

theorem backwardShiftLeft_optimal (result out : BitFact) :
    Le result out → Le (backwardShiftLeft result) out := by
  simpa [backwardShiftLeft]

theorem backwardShiftRight_optimal (result out : BitFact) :
    Le result out → Le (backwardShiftRight result) out := by
  simpa [backwardShiftRight]

theorem backwardMergeHi_optimal (result out : BitFact) :
    Le result out → Le (backwardMergeHi result) out := by
  simpa [backwardMergeHi]

theorem backwardMergeLo_optimal (result out : BitFact) :
    Le result out → Le (backwardMergeLo result) out := by
  simpa [backwardMergeLo]

theorem backwardSplitHi_optimal (result out : BitFact) :
    Le result out → Le (backwardSplitHi result) out := by
  simpa [backwardSplitHi]

theorem backwardSplitLo_optimal (result out : BitFact) :
    Le result out → Le (backwardSplitLo result) out := by
  simpa [backwardSplitLo]

theorem backwardSelect_runtime_optimal (result out : BitFact) :
    (Le result out → Le (backwardSelectTrue result) out) ∧
      (Le result out → Le (backwardSelectFalse result) out) ∧
      ((∀ b : Bool, Holds out b) → Le backwardSelectUnknownDistinct out) ∧
      (Le result out → Le (backwardSelectShared result) out) := by
  constructor
  · exact backwardSelectTrue_optimal result out
  constructor
  · exact backwardSelectFalse_optimal result out
  constructor
  · exact backwardSelectUnknownDistinct_optimal out
  · exact backwardSelectShared_optimal result out

theorem backwardMerge_runtime_optimal (result out : BitFact) :
    (Le result out → Le (backwardMergeHi result) out) ∧
      (Le result out → Le (backwardMergeLo result) out) := by
  constructor
  · exact backwardMergeHi_optimal result out
  · exact backwardMergeLo_optimal result out

theorem backwardSplit_runtime_optimal (result out : BitFact) :
    (Le result out → Le (backwardSplitHi result) out) ∧
      (Le result out → Le (backwardSplitLo result) out) := by
  constructor
  · exact backwardSplitHi_optimal result out
  · exact backwardSplitLo_optimal result out

end BitFact

private def selectInt (cond : Bool) (tv fv : Int) : Int :=
  if cond then tv else fv

private theorem powTwoMono {m n : Nat} (h : m ≤ n) :
    ((2 : Int) ^ m) ≤ (2 : Int) ^ n := by
  have hNat : (2 : Nat) ^ m ≤ (2 : Nat) ^ n := Nat.pow_le_pow_right (by decide) h
  exact_mod_cast hNat

private theorem unsignedRangeMono {m n : Nat} (h : m ≤ n) {v : Int} :
    unsignedRange m v → unsignedRange n v := by
  intro hv
  constructor
  · exact hv.1
  · exact lt_of_lt_of_le hv.2 (powTwoMono h)

private theorem signedRangeMono {m n : Nat} (hmn : m ≤ n) (hm : 0 < m) (hn : 0 < n) {v : Int} :
    signedRange m v → signedRange n v := by
  intro hv
  have hpred : m - 1 ≤ n - 1 := by omega
  have hpow : ((2 : Int) ^ (m - 1)) ≤ (2 : Int) ^ (n - 1) := powTwoMono hpred
  constructor
  · exact le_trans (by simpa [Int.neg_le_neg_iff] using hpow) hv.1
  · exact le_trans hv.2 (sub_le_sub_right hpow 1)

private theorem rankUnsignedUnsigned {lhs rhs : Nat} (h : lhs ≤ rhs) :
    annotationRankLe (.unsigned lhs) (.unsigned rhs) := by
  unfold annotationRankLe annotationRank
  rcases lt_or_eq_of_le h with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, by decide⟩

private theorem rankUnsignedSigned {lhs rhs : Nat} (h : lhs ≤ rhs) :
    annotationRankLe (.unsigned lhs) (.signed rhs) := by
  unfold annotationRankLe annotationRank
  rcases lt_or_eq_of_le h with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, by decide⟩

private theorem rankSignedSigned {lhs rhs : Nat} (h : lhs ≤ rhs) :
    annotationRankLe (.signed lhs) (.signed rhs) := by
  unfold annotationRankLe annotationRank
  rcases lt_or_eq_of_le h with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, by decide⟩

private theorem rankSignedUnsigned {lhs rhs : Nat} (h : lhs < rhs) :
    annotationRankLe (.signed lhs) (.unsigned rhs) := by
  unfold annotationRankLe annotationRank
  exact Or.inl h

private def tightenedSignedUpper (u s : Option Nat) : Option Nat :=
  match u, s with
  | some ub, some sb => some (Nat.min sb ub.succ)
  | some ub, none => some ub.succ
  | none, some sb => some sb
  | none, none => none

private def maxBound : Option Nat → Option Nat → Option Nat
  | some lhs, some rhs => some (Nat.max lhs rhs)
  | _, _ => none

private def minBound : Option Nat → Option Nat → Option Nat
  | some lhs, some rhs => some (Nat.min lhs rhs)
  | _, _ => none

private def widthOnlyFacts (u s : Option Nat) : IntFacts :=
  {
    isBottom := false
    knownZero := 0
    knownOne := 0
    unsignedWidthUpperBound := u
    signedWidthUpperBound := tightenedSignedUpper u s
  }

private def exactUnsignedWidth (v : Int) : Option Nat :=
  if 0 ≤ v then some (Nat.max v.toNat.size 1) else none

private def exactSignedWidth (v : Int) : Nat :=
  if 0 ≤ v then Nat.succ v.toNat.size
  else Nat.succ (((-v) - 1).toNat.size)

private def constSummaryFacts (v : Int) : IntFacts :=
  widthOnlyFacts (exactUnsignedWidth v) (some (exactSignedWidth v))

private def selectSummaryFacts (lhs rhs : IntFacts) : IntFacts :=
  widthOnlyFacts
    (maxBound lhs.unsignedWidthUpperBound rhs.unsignedWidthUpperBound)
    (maxBound lhs.signedWidthUpperBound rhs.signedWidthUpperBound)

private def bitAndSummaryFacts (lhs rhs : IntFacts) : IntFacts :=
  widthOnlyFacts (minBound lhs.unsignedWidthUpperBound rhs.unsignedWidthUpperBound) none

private def bitOrSummaryFacts (lhs rhs : IntFacts) : IntFacts :=
  widthOnlyFacts
    (maxBound lhs.unsignedWidthUpperBound rhs.unsignedWidthUpperBound)
    none

private def bitXorSummaryFacts (lhs rhs : IntFacts) : IntFacts :=
  bitOrSummaryFacts lhs rhs

private def splitLoSummaryFacts (width : Nat) : IntFacts :=
  widthOnlyFacts (some (Nat.max width 1)) none

theorem supportsSummaryAnnotation_sound
    (facts : IntFacts) (ann : Annotation)
    (hwell : facts.WellFormed)
    (hs : facts.SupportsSummaryAnnotation ann) :
    ∀ v : Int, facts.Realizes v → applyAnnotation v ann = .int v := by
  intro v hv
  rcases hv with ⟨_, _, _, hUnsigned, hSigned⟩
  rcases hwell with ⟨_, hUnsignedWF, hSignedWF, _⟩
  cases ann with
  | signed bits =>
      rcases hs with ⟨_, ub, hub, hubLe⟩
      have hvRange := hSigned ub hub
      have hubPos : 0 < ub := hSignedWF _ hub
      have hbitsPos : 0 < bits := lt_of_lt_of_le hubPos hubLe
      have hwiden := signedRangeMono hubLe hubPos hbitsPos hvRange
      simpa [applyAnnotation, checkSignedRange, signedRange] using hwiden
  | unsigned bits =>
      rcases hs with ⟨_, ub, hub, hubLe⟩
      have hwiden := unsignedRangeMono hubLe (hUnsigned ub hub)
      simpa [applyAnnotation, checkUnsignedRange, unsignedRange] using hwiden
  | dontCare _ => cases hs
  | known _ => cases hs
  | align _ => cases hs

theorem bestAnnotation_supportsSummary
    (facts : IntFacts) (ann : Annotation)
    (hbest : facts.bestAnnotation = some ann) :
    facts.SupportsSummaryAnnotation ann := by
  unfold IntFacts.bestAnnotation at hbest
  cases hbot : facts.isBottom <;> simp [hbot] at hbest
  case false =>
    cases hu : facts.unsignedWidthUpperBound with
    | none =>
        cases hs : facts.signedWidthUpperBound with
        | none =>
            simp [hu, hs] at hbest
        | some sb =>
            simp [hu, hs] at hbest
            cases hbest
            exact ⟨hbot, sb, hs, le_rfl⟩
    | some ub =>
        cases hs : facts.signedWidthUpperBound with
        | none =>
            simp [hu, hs] at hbest
            cases hbest
            exact ⟨hbot, ub, hu, le_rfl⟩
        | some sb =>
            by_cases hchoose : sb < ub
            · simp [hu, hs, hchoose] at hbest
              cases hbest
              exact ⟨hbot, sb, hs, le_rfl⟩
            · simp [hu, hs, hchoose] at hbest
              cases hbest
              exact ⟨hbot, ub, hu, le_rfl⟩

theorem bestAnnotation_sound
    (facts : IntFacts) (ann : Annotation)
    (hwell : facts.WellFormed)
    (hbest : facts.bestAnnotation = some ann) :
    ∀ v : Int, facts.Realizes v → applyAnnotation v ann = .int v := by
  exact supportsSummaryAnnotation_sound facts ann hwell
    (bestAnnotation_supportsSummary facts ann hbest)

theorem bestAnnotation_minimal
    (facts : IntFacts) (best candidate : Annotation)
    (hbest : facts.bestAnnotation = some best)
    (hsupport : facts.SupportsSummaryAnnotation candidate) :
    annotationRankLe best candidate := by
  cases candidate with
  | unsigned bits =>
      rcases hsupport with ⟨hbot, ubc, hubc, hubcLe⟩
      unfold IntFacts.bestAnnotation at hbest
      simp [hbot] at hbest
      cases hu : facts.unsignedWidthUpperBound with
      | none =>
          simp [IntFacts.SupportsSummaryAnnotation, hu] at hubc
      | some ub =>
          cases hs : facts.signedWidthUpperBound with
          | none =>
              simp [hu, hs] at hbest
              cases hbest
              have hubEq : ubc = ub := by
                simp [hu] at hubc
                simpa using hubc.symm
              subst hubEq
              exact rankUnsignedUnsigned hubcLe
          | some sb =>
              by_cases hchoose : sb < ub
              · simp [hu, hs, hchoose] at hbest
                cases hbest
                have hubEq : ubc = ub := by
                  simp [hu] at hubc
                  simpa using hubc.symm
                subst hubEq
                exact rankSignedUnsigned (lt_of_lt_of_le hchoose hubcLe)
              · simp [hu, hs, hchoose] at hbest
                cases hbest
                have hubEq : ubc = ub := by
                  simp [hu] at hubc
                  simpa using hubc.symm
                subst hubEq
                exact rankUnsignedUnsigned hubcLe
  | signed bits =>
      rcases hsupport with ⟨hbot, ubc, hubc, hubcLe⟩
      unfold IntFacts.bestAnnotation at hbest
      simp [hbot] at hbest
      cases hu : facts.unsignedWidthUpperBound with
      | none =>
          cases hs : facts.signedWidthUpperBound with
          | none =>
              simp [IntFacts.SupportsSummaryAnnotation, hs] at hubc
          | some sb =>
              simp [hu, hs] at hbest
              cases hbest
              have hubEq : ubc = sb := by
                simp [hs] at hubc
                simpa using hubc.symm
              subst hubEq
              exact rankSignedSigned hubcLe
      | some ub =>
          cases hs : facts.signedWidthUpperBound with
          | none =>
              simp [IntFacts.SupportsSummaryAnnotation, hs] at hubc
          | some sb =>
              by_cases hchoose : sb < ub
              · simp [hu, hs, hchoose] at hbest
                cases hbest
                have hubEq : ubc = sb := by
                  simp [hs] at hubc
                  simpa using hubc.symm
                subst hubEq
                exact rankSignedSigned hubcLe
              · simp [hu, hs, hchoose] at hbest
                cases hbest
                have hubEq : ubc = sb := by
                  simp [hs] at hubc
                  simpa using hubc.symm
                subst hubEq
                have hubLeBits : ub ≤ bits := le_trans (Nat.le_of_not_lt hchoose) hubcLe
                exact rankUnsignedSigned hubLeBits
  | dontCare _ => cases hsupport
  | known _ => cases hsupport
  | align _ => cases hsupport

theorem intAnnotationForward_const_optimal
    (v : Int) (ann candidate : Annotation)
    (hbest : (constSummaryFacts v).bestAnnotation = some ann)
    (hsupport : (constSummaryFacts v).SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationForward_select_optimal
    (lhs rhs : IntFacts) (ann candidate : Annotation)
    (hbest : (selectSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (selectSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationForward_bitAnd_optimal
    (lhs rhs : IntFacts) (ann candidate : Annotation)
    (hbest : (bitAndSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (bitAndSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationForward_bitOr_optimal
    (lhs rhs : IntFacts) (ann candidate : Annotation)
    (hbest : (bitOrSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (bitOrSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationForward_bitXor_optimal
    (lhs rhs : IntFacts) (ann candidate : Annotation)
    (hbest : (bitXorSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (bitXorSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationForward_splitLo_optimal
    (width : Nat) (ann candidate : Annotation)
    (hbest : (splitLoSummaryFacts width).bestAnnotation = some ann)
    (hsupport : (splitLoSummaryFacts width).SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationBackward_select_optimal
    (facts : IntFacts) (ann candidate : Annotation)
    (hbest : facts.bestAnnotation = some ann)
    (hsupport : facts.SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem intAnnotationBackward_split_optimal
    (facts : IntFacts) (ann candidate : Annotation)
    (hbest : facts.bestAnnotation = some ann)
    (hsupport : facts.SupportsSummaryAnnotation candidate) :
    annotationRankLe ann candidate := by
  exact bestAnnotation_minimal _ _ _ hbest hsupport

theorem resultFact_const_optimal
    (bit : Bool) (out : BitFact) (v : Int)
    (ann candidate : Annotation)
    (hbit : BitFact.Holds out bit)
    (hbest : (constSummaryFacts v).bestAnnotation = some ann)
    (hsupport : (constSummaryFacts v).SupportsSummaryAnnotation candidate) :
    BitFact.Le (BitFact.exactBit bit) out ∧ annotationRankLe ann candidate := by
  constructor
  · exact BitFact.exactBit_optimal bit out hbit
  · exact intAnnotationForward_const_optimal v ann candidate hbest hsupport

theorem resultFact_select_optimal
    (tv fv out : BitFact) (lhs rhs : IntFacts)
    (ann candidate : Annotation)
    (hkb : BitFact.SelectForwardSound tv fv out)
    (hbest : (selectSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (selectSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    BitFact.Le (BitFact.forwardSelect tv fv) out ∧ annotationRankLe ann candidate := by
  constructor
  · exact BitFact.forwardSelect_optimal tv fv out hkb
  · exact intAnnotationForward_select_optimal lhs rhs ann candidate hbest hsupport

theorem resultFact_bitAnd_optimal
    (lhsBit rhsBit out : BitFact) (lhs rhs : IntFacts)
    (ann candidate : Annotation)
    (hkb : BitFact.ForwardSound Bool.and lhsBit rhsBit out)
    (hbest : (bitAndSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (bitAndSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    BitFact.Le (BitFact.forwardBitAnd lhsBit rhsBit) out ∧ annotationRankLe ann candidate := by
  constructor
  · exact BitFact.forwardBitAnd_optimal lhsBit rhsBit out hkb
  · exact intAnnotationForward_bitAnd_optimal lhs rhs ann candidate hbest hsupport

theorem resultFact_bitOr_optimal
    (lhsBit rhsBit out : BitFact) (lhs rhs : IntFacts)
    (ann candidate : Annotation)
    (hkb : BitFact.ForwardSound Bool.or lhsBit rhsBit out)
    (hbest : (bitOrSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (bitOrSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    BitFact.Le (BitFact.forwardBitOr lhsBit rhsBit) out ∧ annotationRankLe ann candidate := by
  constructor
  · exact BitFact.forwardBitOr_optimal lhsBit rhsBit out hkb
  · exact intAnnotationForward_bitOr_optimal lhs rhs ann candidate hbest hsupport

theorem resultFact_bitXor_optimal
    (lhsBit rhsBit out : BitFact) (lhs rhs : IntFacts)
    (ann candidate : Annotation)
    (hkb : BitFact.ForwardSound xor lhsBit rhsBit out)
    (hbest : (bitXorSummaryFacts lhs rhs).bestAnnotation = some ann)
    (hsupport : (bitXorSummaryFacts lhs rhs).SupportsSummaryAnnotation candidate) :
    BitFact.Le (BitFact.forwardBitXor lhsBit rhsBit) out ∧ annotationRankLe ann candidate := by
  constructor
  · exact BitFact.forwardBitXor_optimal lhsBit rhsBit out hkb
  · exact intAnnotationForward_bitXor_optimal lhs rhs ann candidate hbest hsupport

theorem resultFact_splitLo_optimal
    (src out : BitFact) (width : Nat)
    (ann candidate : Annotation)
    (hkb : BitFact.Le src out)
    (hbest : (splitLoSummaryFacts width).bestAnnotation = some ann)
    (hsupport : (splitLoSummaryFacts width).SupportsSummaryAnnotation candidate) :
    BitFact.Le (BitFact.forwardSplitLo src) out ∧ annotationRankLe ann candidate := by
  constructor
  · exact BitFact.forwardSplitLo_optimal src out hkb
  · exact intAnnotationForward_splitLo_optimal width ann candidate hbest hsupport

theorem resultFact_shl_optimal
    (fillsZero : Bool) (src out : BitFact)
    (hkb : if fillsZero then BitFact.Holds out false else BitFact.Le src out) :
    BitFact.Le (BitFact.forwardShiftLeft fillsZero src) out := by
  exact BitFact.forwardShiftLeft_optimal fillsZero src out hkb

theorem resultFact_shr_optimal
    (src out : BitFact)
    (hkb : BitFact.Le src out) :
    BitFact.Le (BitFact.forwardShiftRight src) out := by
  exact BitFact.forwardShiftRight_optimal src out hkb

theorem resultFact_merge_optimal
    (takeLow : Bool) (hi lo out : BitFact)
    (hkb : if takeLow then BitFact.Le lo out else BitFact.Le hi out) :
    BitFact.Le (BitFact.forwardMerge takeLow hi lo) out := by
  exact BitFact.forwardMerge_optimal takeLow hi lo out hkb

theorem resultFact_splitHi_optimal
    (src out : BitFact)
    (hkb : BitFact.Le src out) :
    BitFact.Le (BitFact.forwardSplitHi src) out := by
  exact BitFact.forwardSplitHi_optimal src out hkb

theorem instFact_bitAnd_optimal
    (rhs result out : BitFact)
    (hex : ∃ a b : Bool, BitFact.Holds rhs b ∧ BitFact.Holds result (Bool.and a b))
    (hsound : BitFact.BackwardSoundL Bool.and rhs result out) :
    BitFact.Le (BitFact.backwardBitAndL rhs result) out := by
  exact BitFact.backwardBitAndL_optimal rhs result out hex hsound

theorem instFact_bitOr_optimal
    (rhs result out : BitFact)
    (hex : ∃ a b : Bool, BitFact.Holds rhs b ∧ BitFact.Holds result (Bool.or a b))
    (hsound : BitFact.BackwardSoundL Bool.or rhs result out) :
    BitFact.Le (BitFact.backwardBitOrL rhs result) out := by
  exact BitFact.backwardBitOrL_optimal rhs result out hex hsound

theorem instFact_bitXor_optimal
    (rhs result out : BitFact)
    (hex : ∃ a b : Bool, BitFact.Holds rhs b ∧ BitFact.Holds result (xor a b))
    (hsound : BitFact.BackwardSoundL xor rhs result out) :
    BitFact.Le (BitFact.backwardBitXorL rhs result) out := by
  exact BitFact.backwardBitXorL_optimal rhs result out hex hsound

theorem instFact_shl_optimal
    (result out : BitFact)
    (hkb : BitFact.Le result out) :
    BitFact.Le (BitFact.backwardShiftLeft result) out := by
  exact BitFact.backwardShiftLeft_optimal result out hkb

theorem instFact_shr_optimal
    (result out : BitFact)
    (hkb : BitFact.Le result out) :
    BitFact.Le (BitFact.backwardShiftRight result) out := by
  exact BitFact.backwardShiftRight_optimal result out hkb

theorem instFact_merge_optimal
    (result out : BitFact) :
    (BitFact.Le result out → BitFact.Le (BitFact.backwardMergeHi result) out) ∧
      (BitFact.Le result out → BitFact.Le (BitFact.backwardMergeLo result) out) := by
  exact BitFact.backwardMerge_runtime_optimal result out

theorem instFact_select_optimal
    (result out : BitFact) (facts : IntFacts)
    (ann candidate : Annotation)
    (hbest : facts.bestAnnotation = some ann)
    (hsupport : facts.SupportsSummaryAnnotation candidate) :
    ((BitFact.Le result out → BitFact.Le (BitFact.backwardSelectTrue result) out) ∧
      (BitFact.Le result out → BitFact.Le (BitFact.backwardSelectFalse result) out) ∧
      ((∀ b : Bool, BitFact.Holds out b) → BitFact.Le BitFact.backwardSelectUnknownDistinct out) ∧
      (BitFact.Le result out → BitFact.Le (BitFact.backwardSelectShared result) out)) ∧
      annotationRankLe ann candidate := by
  constructor
  · exact BitFact.backwardSelect_runtime_optimal result out
  · exact intAnnotationBackward_select_optimal facts ann candidate hbest hsupport

theorem instFact_split_optimal
    (result out : BitFact) (facts : IntFacts)
    (ann candidate : Annotation)
    (hbest : facts.bestAnnotation = some ann)
    (hsupport : facts.SupportsSummaryAnnotation candidate) :
    ((BitFact.Le result out → BitFact.Le (BitFact.backwardSplitHi result) out) ∧
      (BitFact.Le result out → BitFact.Le (BitFact.backwardSplitLo result) out)) ∧
      annotationRankLe ann candidate := by
  constructor
  · exact BitFact.backwardSplit_runtime_optimal result out
  · exact intAnnotationBackward_split_optimal facts ann candidate hbest hsupport

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

theorem atUseForward_add_sound (a b : Int) :
    evalAdd a b = a + b := by
  rfl

theorem atUseForward_sub_sound (a b : Int) :
    evalSub a b = a - b := by
  rfl

theorem atUseForward_shr_sound (a b : Int) (h : 0 ≤ b) :
    evalShr a b = .int (a >>> b.toNat) := by
  simp [evalShr, h]

theorem atUseForward_zext_sound (v : Int) (n : Nat) :
    applyAnnotation v (.dontCare n) = .int (v % (2 ^ n)) := by
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
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_const_optimal"
    },
    {
      op := "select"
      result := .primary
      knownBitsForward := .select
      intAnnotationForward := .select
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_select_optimal"
    },
    {
      op := "and"
      result := .primary
      knownBitsForward := .bitAnd
      intAnnotationForward := .bitAnd
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_bitAnd_optimal"
    },
    {
      op := "or"
      result := .primary
      knownBitsForward := .bitOr
      intAnnotationForward := .bitOr
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_bitOr_optimal"
    },
    {
      op := "xor"
      result := .primary
      knownBitsForward := .bitXor
      intAnnotationForward := .bitXor
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_bitXor_optimal"
    },
    {
      op := "shl"
      result := .primary
      knownBitsForward := .shl
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_shl_optimal"
    },
    {
      op := "shr"
      result := .primary
      knownBitsForward := .shr
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_shr_optimal"
    },
    {
      op := "merge"
      result := .primary
      knownBitsForward := .merge
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_merge_optimal"
    },
    {
      op := "split"
      result := .primary
      knownBitsForward := .splitHi
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_splitHi_optimal"
    },
    {
      op := "split"
      result := .secondary
      knownBitsForward := .splitLo
      intAnnotationForward := .splitLo
      proofRef := "TuffyLean.Rewrites.Facts.resultFact_splitLo_optimal"
    }
  ]

def instFactRules : List InstFactRule :=
  [
    {
      op := "select"
      knownBitsBackward := .select
      intAnnotationBackward := .select
      proofRef := "TuffyLean.Rewrites.Facts.instFact_select_optimal"
    },
    {
      op := "and"
      knownBitsBackward := .bitAnd
      proofRef := "TuffyLean.Rewrites.Facts.instFact_bitAnd_optimal"
    },
    {
      op := "or"
      knownBitsBackward := .bitOr
      proofRef := "TuffyLean.Rewrites.Facts.instFact_bitOr_optimal"
    },
    {
      op := "xor"
      knownBitsBackward := .bitXor
      proofRef := "TuffyLean.Rewrites.Facts.instFact_bitXor_optimal"
    },
    {
      op := "shl"
      knownBitsBackward := .shl
      proofRef := "TuffyLean.Rewrites.Facts.instFact_shl_optimal"
    },
    {
      op := "shr"
      knownBitsBackward := .shr
      proofRef := "TuffyLean.Rewrites.Facts.instFact_shr_optimal"
    },
    {
      op := "merge"
      knownBitsBackward := .merge
      proofRef := "TuffyLean.Rewrites.Facts.instFact_merge_optimal"
    },
    {
      op := "split"
      knownBitsBackward := .split
      intAnnotationBackward := .split
      proofRef := "TuffyLean.Rewrites.Facts.instFact_split_optimal"
    }
  ]

end TuffyLean.Rewrites.Facts

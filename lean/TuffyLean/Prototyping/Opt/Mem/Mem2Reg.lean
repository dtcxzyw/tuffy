-- TuffyLean/Prototyping/Opt/Mem/Mem2Reg.lean
-- Prototype CFG/block-arg specification for stack promotion.

import TuffyLean.IR.Types
import TuffyLean.IR.Semantics

namespace TuffyLean.Prototyping.Opt.Mem2Reg

open TuffyLean.IR

abbrev BlockId := Nat
abbrev SlotId := Nat

/-- Minimal CFG model used by the mem2reg prototype. -/
structure CFG where
  entry : BlockId
  succs : BlockId → List BlockId

/-- Paths start at the CFG entry and end at the requested block. -/
inductive Path (cfg : CFG) : BlockId → List BlockId → Prop where
  | entry : Path cfg cfg.entry [cfg.entry]
  | step {block target path}
      (hpath : Path cfg block path)
      (hedge : target ∈ cfg.succs block) :
      Path cfg target (path ++ [target])

/-- Reachability from the CFG entry. -/
def Reachable (cfg : CFG) (block : BlockId) : Prop :=
  ∃ path, Path cfg block path

/-- Standard path-based dominance relation. -/
def Dominates (cfg : CFG) (dom block : BlockId) : Prop :=
  ∀ path, Path cfg block path → dom ∈ path

theorem entry_mem_of_path {cfg : CFG} {block : BlockId} {path : List BlockId}
    (hpath : Path cfg block path) : cfg.entry ∈ path := by
  induction hpath with
  | entry =>
      simp
  | step hpath _ ih =>
      exact List.mem_append.mpr (.inl ih)

theorem entry_dominates_reachable (cfg : CFG) {block : BlockId}
    (_hreach : Reachable cfg block) : Dominates cfg cfg.entry block := by
  intro path hpath
  exact entry_mem_of_path hpath

/-- Current renamed SSA value for each promoted slot. -/
structure RenameState where
  current : SlotId → Value

namespace RenameState

/-- Read the current SSA name/value for a promoted slot. -/
def load (state : RenameState) (slot : SlotId) : Value :=
  state.current slot

/-- Update the current SSA name/value after a promoted store. -/
def store (state : RenameState) (slot : SlotId) (value : Value) : RenameState where
  current := fun query => if query = slot then value else state.current query

/-- Apply a sequence of promoted stores along one edge or one block. -/
def stores (state : RenameState) : List (SlotId × Value) → RenameState
  | [] => state
  | (slot, value) :: rest => stores (state.store slot value) rest

theorem load_after_store_same (state : RenameState) (slot : SlotId) (value : Value) :
    (state.store slot value).load slot = value := by
  simp [load, store]

theorem load_after_store_other (state : RenameState) {slot other : SlotId} (value : Value)
    (hneq : other ≠ slot) :
    (state.store slot value).load other = state.load other := by
  simp [load, store, hneq]

theorem load_after_two_stores_same (state : RenameState) (slot : SlotId)
    (value₁ value₂ : Value) :
    ((state.store slot value₁).store slot value₂).load slot = value₂ := by
  simp [load, store]

theorem stores_nil (state : RenameState) :
    state.stores [] = state := rfl

theorem stores_cons (state : RenameState) (slot : SlotId) (value : Value)
    (rest : List (SlotId × Value)) :
    state.stores ((slot, value) :: rest) = (state.store slot value).stores rest := rfl

end RenameState

/-- Incoming renamed state per predecessor edge. Block arguments implement this join. -/
abbrev IncomingStates := BlockId → RenameState

/-- The block-argument join chosen on control-flow edge `pred -> block`. -/
def joinState (incoming : IncomingStates) (pred : BlockId) : RenameState :=
  incoming pred

theorem joinState_load_eq_incoming (incoming : IncomingStates) (pred : BlockId) (slot : SlotId) :
    (joinState incoming pred).current slot = (incoming pred).current slot := rfl

theorem block_arg_join_observes_predecessor_store
    (state : RenameState) (pred : BlockId) (slot : SlotId) (value : Value) :
    (joinState (fun edge => if edge = pred then state.store slot value else state) pred).load slot
      = value := by
  simp [joinState, RenameState.load, RenameState.store]

theorem block_arg_join_preserves_other_slot
    (state : RenameState) (pred : BlockId) {slot other : SlotId} (value : Value)
    (hneq : other ≠ slot) :
    (joinState (fun edge => if edge = pred then state.store slot value else state) pred).load other
      = state.load other := by
  simp [joinState, RenameState.load, RenameState.store, hneq]

theorem block_arg_join_after_store_sequence
    (state : RenameState) (pred : BlockId) (stores : List (SlotId × Value)) (slot : SlotId) :
    (joinState (fun edge => if edge = pred then state.stores stores else state) pred).load slot
      = (state.stores stores).load slot := by
  simp [joinState, RenameState.load]

end TuffyLean.Prototyping.Opt.Mem2Reg

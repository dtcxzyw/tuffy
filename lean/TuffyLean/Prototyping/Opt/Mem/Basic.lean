-- TuffyLean/Prototyping/Opt/Mem/Basic.lean
-- Prototype memory optimizations to validate IR design.
-- These are NOT part of the production optimization pipeline (see Rewrites/).

import TuffyLean.IR.Types
import TuffyLean.IR.Semantics

namespace TuffyLean.Prototyping.Opt.Mem

open TuffyLean.IR

/-! ## Store-Load Forwarding

If bytes `bs` are stored to address `p`, then loading `bs.length` bytes
from the same address `p` yields exactly `bs`. This validates that the
IR's memory model supports the most fundamental memory optimization. -/

theorem store_load_forward (mem : Memory) (addr : Int) (bs : List AbstractByte) :
    evalLoad (evalStore mem addr bs) addr bs.length = .bytes bs := by
  simp only [evalLoad, evalStore]
  congr 1
  have key : ∀ (i : Fin bs.length),
      (if 0 ≤ addr + ↑↑i - addr ∧ addr + ↑↑i - addr < ↑bs.length
       then bs.getD (addr + ↑↑i - addr).toNat AbstractByte.uninit
       else mem.bytes (addr + ↑↑i)) = bs.get i := by
    intro ⟨i, hi⟩
    simp only [show addr + (↑i : Int) - addr = ↑i from by omega]
    have h1 : (0 : Int) ≤ ↑i := Int.natCast_nonneg i
    have h2 : (↑i : Int) < ↑bs.length := by exact_mod_cast hi
    simp only [h1, h2, and_self, ↓reduceIte, Int.toNat_natCast]
    exact List.getD_eq_getElem bs AbstractByte.uninit hi
  simp_rw [key]
  exact List.ofFn_get bs

/-! ## Load-Store Redundancy (Dead Store Elimination)

If we load bytes from address `p` and immediately store them back to `p`,
the memory is unchanged — the store is redundant and can be eliminated. -/

theorem load_store_redundant (mem : Memory) (addr : Int) (size : Nat) :
    evalStore mem addr (List.ofFn (fun (i : Fin size) => mem.bytes (addr + ↑i.val)))
    = mem := by
  simp only [evalStore]
  cases mem with | mk bytes =>
  simp only [Memory.mk.injEq]
  funext a
  simp only [List.length_ofFn]
  by_cases h : 0 ≤ a - addr ∧ a - addr < ↑size
  · simp only [h, and_self, ite_true]
    have hnat : (a - addr).toNat < size := by omega
    rw [List.getD_eq_getElem _ AbstractByte.uninit (by rw [List.length_ofFn]; exact hnat)]
    rw [List.getElem_ofFn]
    rw [show (⟨(a - addr).toNat, hnat⟩ : Fin size).val = (a - addr).toNat from rfl]
    rw [Int.toNat_of_nonneg h.1]
    congr 1; omega
  · simp only [h, ite_false]

end TuffyLean.Prototyping.Opt.Mem

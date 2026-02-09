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

/-! ## Load-Load Consistency

Two loads from the same memory at the same address and size always produce
the same result. This is immediate because `evalLoad` is a pure function. -/

theorem load_load_same (mem : Memory) (addr : Int) (size : Nat) :
    evalLoad mem addr size = evalLoad mem addr size := rfl

/-! ## Load After Non-Aliasing Store

If a store writes to an address range that does not overlap with the load
address range, the load result is unchanged. This validates that the IR's
memory model correctly supports alias analysis optimizations. -/

theorem load_after_noalias_store (mem : Memory) (storeAddr loadAddr : Int)
    (bs : List AbstractByte) (size : Nat)
    (h_noalias : ∀ i : Fin size, ∀ j : Fin bs.length,
      loadAddr + ↑i.val ≠ storeAddr + ↑j.val) :
    evalLoad (evalStore mem storeAddr bs) loadAddr size = evalLoad mem loadAddr size := by
  simp only [evalLoad, evalStore]
  congr 1
  have key : ∀ (i : Fin size),
      (if 0 ≤ loadAddr + ↑↑i - storeAddr ∧ loadAddr + ↑↑i - storeAddr < ↑bs.length
       then bs.getD (loadAddr + ↑↑i - storeAddr).toNat AbstractByte.uninit
       else mem.bytes (loadAddr + ↑↑i)) = mem.bytes (loadAddr + ↑↑i) := by
    intro ⟨i, hi⟩
    simp only
    split
    · next h =>
      exfalso
      have h1 := h.1
      have hj : (loadAddr + ↑i - storeAddr).toNat < bs.length := by omega
      set offset := loadAddr + (↑i : Int) - storeAddr with hoff
      have cast_eq : (↑offset.toNat : Int) = offset := Int.toNat_of_nonneg h1
      have addr_eq : loadAddr + (↑i : Int) = storeAddr + (↑offset.toNat : Int) := by
        rw [cast_eq, hoff]; omega
      exact h_noalias ⟨i, hi⟩ ⟨offset.toNat, hj⟩ addr_eq
    · rfl
  simp_rw [key]

/-! ## Store-Store Same Address (Dead Store Elimination)

If two stores target the same address and the second store covers at least
as many bytes as the first, the first store is completely overwritten and
can be eliminated. -/

theorem store_store_same_addr (mem : Memory) (addr : Int)
    (bs1 bs2 : List AbstractByte) (h_cover : bs1.length ≤ bs2.length) :
    evalStore (evalStore mem addr bs1) addr bs2 = evalStore mem addr bs2 := by
  simp only [evalStore]
  cases mem with | mk bytes =>
  simp only [Memory.mk.injEq]
  funext a
  by_cases h : 0 ≤ a - addr ∧ a - addr < ↑bs2.length
  · simp only [h, and_self, ite_true]
  · simp only [h, ite_false]
    have h2 : ¬(0 ≤ a - addr ∧ a - addr < ↑bs1.length) := by
      intro ⟨h1, h3⟩
      exact h ⟨h1, by omega⟩
    simp only [h2, ite_false]

end TuffyLean.Prototyping.Opt.Mem

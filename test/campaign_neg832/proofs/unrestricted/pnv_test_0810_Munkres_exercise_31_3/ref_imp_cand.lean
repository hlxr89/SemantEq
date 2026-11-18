import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- The input preambles have no local definitions or structures.
-- This auxiliary finite order supplies a counterexample to both universal statements.
inductive BadOrder
  | isolated | low | high
  deriving DecidableEq, Fintype

instance : PartialOrder BadOrder where
  le a b := a = b ∨ (a = .low ∧ b = .high)
  lt a b := a = .low ∧ b = .high
  le_refl := by decide
  le_trans := by decide
  lt_iff_le_not_ge := by decide
  le_antisymm := by decide

local instance badTopology : TopologicalSpace BadOrder := Preorder.topology BadOrder
local instance : OrderTopology BadOrder := ⟨rfl⟩

theorem generic_specializes : BadOrder.high ⤳ BadOrder.isolated := by
  have hiso : nhds BadOrder.isolated = ⊤ := by
    rw [nhds_generateFrom]
    simp only [iInf_eq_top, mem_setOf_eq]
    intro s hs
    rcases hs with ⟨hs, a, rfl | rfl⟩ <;> simp [instPartialOrderBadOrder] at hs
  rw [specializes_iff_nhds, hiso]
  exact le_top

theorem not_reverse_specializes : ¬ (BadOrder.isolated ⤳ BadOrder.high) := by
  rw [not_specializes_iff_exists_open]
  exact ⟨Ioi .low, isOpen_Ioi' _, by simp [instPartialOrderBadOrder],
    by simp [instPartialOrderBadOrder]⟩

-- ===== assumed statement (antecedent) =====
theorem exercise_31_3_assumed {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {α : Type u} [PartialOrder α] [t : TopologicalSpace α] [t' : OrderTopology α] : T2Space α := by
  letI : RegularSpace BadOrder := exercise_31_3_assumed (α := BadOrder) (by infer_instance)
  have hf : False := not_reverse_specializes generic_specializes.symm
  exact hf.elim

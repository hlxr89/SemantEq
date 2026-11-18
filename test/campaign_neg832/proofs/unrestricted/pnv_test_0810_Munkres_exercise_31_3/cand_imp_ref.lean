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

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type u} [PartialOrder α] [t : TopologicalSpace α] [t' : OrderTopology α] : T2Space α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_31_3 {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  letI : T2Space BadOrder := dummy_assumed (α := BadOrder)
  have hf : False := by
    have heq : BadOrder.high = BadOrder.isolated := specializes_iff_eq.mp generic_specializes
    simpa using heq
  exact hf.elim

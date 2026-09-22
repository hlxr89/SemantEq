import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] : ∃ H : Subgroup G, Normal H ∧ ¬ Characteristic H := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  exfalso
  obtain ⟨H, _, hH⟩ := dummy_assumed Unit
  apply hH
  have : H = (⊤ : Subgroup Unit) := by
    ext x
    simp only [mem_top, iff_true]
    simpa using H.one_mem
  rw [this]
  infer_instance

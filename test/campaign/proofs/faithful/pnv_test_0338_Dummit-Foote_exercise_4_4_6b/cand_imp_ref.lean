import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] : ∃ (N : Subgroup G), N.Normal ∧ ¬ N.Characteristic := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  obtain ⟨N, hN_normal, hN_not_characteristic⟩ := dummy_assumed (G := PUnit)
  exact ⟨PUnit, inferInstance, N, hN_normal, hN_not_characteristic⟩

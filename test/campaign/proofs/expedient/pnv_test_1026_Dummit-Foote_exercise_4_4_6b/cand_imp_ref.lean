import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] : ∃ H : Subgroup G, H.Normal ∧ ¬ H.Characteristic := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let G : Type _ := ULift.{_, 0} PUnit
  let hG : Group G := inferInstance
  obtain ⟨H, hN, hC⟩ := @dummy_assumed G hG
  exact ⟨G, hG, H, hN, hC⟩

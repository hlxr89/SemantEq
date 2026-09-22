import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] : ∃ (N : Subgroup G), Normal N ∧ ¬Characteristic N := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_6b :
  ∃ (G : Type*) (hG : Group G) (H : @Subgroup G hG), @Normal G hG H ∧ ¬ @Characteristic G hG H := by
  let G := ULift.{u_1} (Equiv.Perm (Fin 3))
  let hG : Group G := inferInstance
  letI : Group G := hG
  obtain ⟨N, hN, hNC⟩ := dummy_assumed G
  exact ⟨G, hG, N, hN, hNC⟩

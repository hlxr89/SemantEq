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
  refine ⟨ULift (Equiv.Perm (Fin 1)), inferInstance, ?_⟩
  exact dummy_assumed (ULift (Equiv.Perm (Fin 1)))

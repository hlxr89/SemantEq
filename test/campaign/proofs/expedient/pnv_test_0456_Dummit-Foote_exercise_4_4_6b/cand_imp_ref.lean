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
  obtain ⟨N, _, hN⟩ := dummy_assumed Unit
  exfalso
  apply hN
  have hEq : N = ⊤ := by
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    exact ⟨fun _ => trivial, fun _ => N.one_mem⟩
  rw [hEq]
  infer_instance

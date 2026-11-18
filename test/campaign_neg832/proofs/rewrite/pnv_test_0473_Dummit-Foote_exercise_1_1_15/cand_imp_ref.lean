import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (G : Type*) [Group G] [DecidableEq G] (a₁ a₂ : G) : (a₁ * a₂)⁻¹ = a₂⁻¹ * a₁⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  classical
  induction as with -- non-rewrite step
  | nil =>
      simp only [List.prod_nil, inv_one, List.reverse_nil, List.map_nil]
  | cons a as ih =>
      rw [List.prod_cons, dummy_assumed G a as.prod, ih]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one]

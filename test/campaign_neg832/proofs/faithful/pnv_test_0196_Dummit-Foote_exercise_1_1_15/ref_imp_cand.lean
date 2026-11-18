import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_15_assumed {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (a1 a2 a3 : G) : (a1 * a2 * a3)⁻¹ = a3⁻¹ * a2⁻¹ * a1⁻¹ := by
  rw [mul_assoc]
  have h := exercise_1_1_15_assumed [a1, a2, a3]
  have h' : (a1 * (a2 * a3))⁻¹ = a3⁻¹ * (a2⁻¹ * a1⁻¹) := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using h
  exact h'.trans (mul_assoc _ _ _).symm

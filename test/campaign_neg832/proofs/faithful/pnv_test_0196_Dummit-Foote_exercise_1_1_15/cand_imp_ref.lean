import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a1 a2 a3 : G) : (a1 * a2 * a3)⁻¹ = a3⁻¹ * a2⁻¹ * a1⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  induction as with
  | nil => simpa using dummy_assumed (1 : G) 1 1
  | cons a as ih =>
      rw [List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton]
      have h : (a * as.prod)⁻¹ = as.prod⁻¹ * a⁻¹ := by
        simpa only [mul_one, inv_one, one_mul] using dummy_assumed a as.prod 1
      rw [h, ih]

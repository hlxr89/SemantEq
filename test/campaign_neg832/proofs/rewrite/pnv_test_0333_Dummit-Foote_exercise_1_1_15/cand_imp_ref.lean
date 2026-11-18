import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (a : G) (n : ℕ) : (a^n)⁻¹ = (a⁻¹)^n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_15 {G : Type*} [Group G] (as : List G) :
  as.prod⁻¹ = (as.reverse.map (λ x => x⁻¹)).prod := by
  conv_lhs =>
    rw [← pow_one as.prod, dummy_assumed, pow_one]
  simpa only [List.map_reverse] using List.prod_inv_reverse as -- non-rewrite step

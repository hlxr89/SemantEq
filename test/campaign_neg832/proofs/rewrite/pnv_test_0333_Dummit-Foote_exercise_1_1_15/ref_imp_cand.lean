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
theorem dummy {G : Type*} [Group G] (a : G) (n : ℕ) : (a^n)⁻¹ = (a⁻¹)^n := by
  simpa only [List.prod_replicate, List.reverse_replicate, List.map_replicate] using
    (exercise_1_1_15_assumed (List.replicate n a))

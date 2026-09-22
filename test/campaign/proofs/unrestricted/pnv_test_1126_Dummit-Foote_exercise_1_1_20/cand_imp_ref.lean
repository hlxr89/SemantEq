import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (x : G) : orderOf x⁻¹ = orderOf x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_20 {G : Type*} [Group G] {x : G} :
  orderOf x = orderOf x⁻¹ := by
  exact (dummy_assumed x).symm

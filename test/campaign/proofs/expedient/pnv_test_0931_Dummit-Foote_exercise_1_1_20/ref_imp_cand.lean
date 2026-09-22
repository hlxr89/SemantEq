import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_20_assumed {G : Type*} [Group G] {x : G} :
  orderOf x = orderOf x⁻¹ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] (x : G) : orderOf (x⁻¹) = orderOf x := by
  exact (exercise_1_1_20_assumed (x := x)).symm

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {a b c : G} : a * b = a * c → b = c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_1_22b {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  exact (SemiconjBy.orderOf_eq a (show SemiconjBy a (b * a) (a * b) by
    simp only [SemiconjBy, mul_assoc])).symm

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_1_22b_assumed {G: Type*} [Group G] (a b : G) :
  orderOf (a * b) = orderOf (b * a) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] {a b c : G} : a * b = a * c → b = c := by
  exact mul_left_cancel

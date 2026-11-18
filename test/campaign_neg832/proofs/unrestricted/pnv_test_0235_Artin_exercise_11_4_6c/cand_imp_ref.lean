import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : Irreducible (Polynomial.X^3 - 9 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine @Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (ZMod 31) _ (X^3 - 9) ?_ ?_
  · norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · intro x
    fin_cases x <;> norm_num [Polynomial.IsRoot] <;> decide

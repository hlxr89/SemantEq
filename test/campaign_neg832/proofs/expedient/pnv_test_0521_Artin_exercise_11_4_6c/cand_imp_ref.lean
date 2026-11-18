import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : Irreducible (X^3 - 9 : Polynomial (Fin 31 → ℤ)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  have hnot' : ∀ x : ZMod 31, x^3 ≠ 9 := by
    native_decide
  have hnot : ∀ x : ZMod 31,
      ¬Polynomial.IsRoot (X^3 - 9 : Polynomial (ZMod 31)) x := by
    intro x hx
    apply hnot' x
    apply sub_eq_zero.mp
    simpa using hx
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  change Irreducible (X^3 - 9 : Polynomial (ZMod 31))
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := (X^3 - 9 : Polynomial (ZMod 31))) ?_ ?_
  · norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · exact hnot

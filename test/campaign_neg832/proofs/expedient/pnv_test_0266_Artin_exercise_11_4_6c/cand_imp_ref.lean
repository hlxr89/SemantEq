import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type _} [Field F] [CharZero F] : Irreducible (X^3 - 9 : F[X]) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_4_6c : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  refine @Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (ZMod 31) inferInstance (X^3 - 9) ?_ ?_
  · norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · intro x
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    fin_cases x <;> decide

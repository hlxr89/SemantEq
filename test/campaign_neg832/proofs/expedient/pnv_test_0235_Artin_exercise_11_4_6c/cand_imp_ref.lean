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
  apply irreducible_of_degree_le_three_of_not_isRoot
  · change (X ^ 3 - C (9 : ZMod 31)).natDegree ∈ Finset.Icc 1 3
    simp
  · suffices ∀ x : ZMod 31, x ^ 3 - 9 ≠ 0 by simpa [IsRoot]
    native_decide

import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_11_4_6c_assumed : Irreducible (X^3 - 9 : Polynomial (ZMod 31)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : Irreducible (Polynomial.X^3 - 9 : Polynomial ℤ) := by
  letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩ -- non-rewrite step
  have hmonic : (Polynomial.X^3 - 9 : Polynomial ℤ).Monic := by
    simpa only [Polynomial.C_ofNat] using
      (Polynomial.monic_X_pow_sub_C (9 : ℤ) (by norm_num : 3 ≠ 0))
  apply hmonic.irreducible_of_irreducible_map (algebraMap ℤ (ZMod 31))
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat] using exercise_11_4_6c_assumed

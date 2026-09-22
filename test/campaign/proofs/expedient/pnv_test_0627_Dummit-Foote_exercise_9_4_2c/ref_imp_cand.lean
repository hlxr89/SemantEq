import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2c_assumed : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (p : Polynomial ℤ) (hp : p = Polynomial.C 1 * Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 1) : Irreducible p := by
  subst p
  convert exercise_9_4_2c_assumed using 1 <;> ext n <;> simp

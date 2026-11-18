import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : Irreducible (Polynomial.C (1 : ℤ) + Polynomial.X + 6 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  -- not proved: the polynomials differ in their linear coefficients and are not related by a rewrite
  sorry

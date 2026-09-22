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
theorem dummy (p : Polynomial ℤ) (hp : p = X^4 + 4*X^3 + 6*X^2 + 2*X + 1) : Irreducible p := by
  subst p
  exact exercise_9_4_2c_assumed

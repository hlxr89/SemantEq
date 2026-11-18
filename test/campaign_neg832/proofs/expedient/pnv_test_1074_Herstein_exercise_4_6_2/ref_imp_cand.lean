import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_2_assumed : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (f : Polynomial ℚ) (hf : f.degree = 3) (hf0 : f.coeff 0 = 2) (hf1 : f.coeff 1 = 3) (hf2 : f.coeff 2 = 1) : Irreducible f := by
  -- not proved: the candidate is false, e.g. for -6*X^3 + X^2 + 3*X + 2
  sorry

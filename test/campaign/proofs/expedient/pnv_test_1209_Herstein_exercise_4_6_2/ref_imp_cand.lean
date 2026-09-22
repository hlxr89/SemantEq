import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_2_assumed : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  exact exercise_4_6_2_assumed

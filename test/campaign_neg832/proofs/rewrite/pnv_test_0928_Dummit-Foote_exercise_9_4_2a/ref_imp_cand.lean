import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2a_assumed : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (x : ℤ[X]) : Irreducible (x^4 - 4*x^3 + 6) := by
  -- not proved: the reference only gives the case x = X, while the candidate quantifies over every polynomial x
  sorry

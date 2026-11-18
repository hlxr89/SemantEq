import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_2_assumed : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [Ring R] (f : Polynomial R) : Irreducible f → f = (X^3 + 3*X + 2 : Polynomial R) := by
  -- not proved: the antecedent concerns one polynomial over ℚ, but the goal quantifies over every ring and irreducible polynomial
  sorry

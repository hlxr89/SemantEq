import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Ring R] (f : Polynomial R) : Irreducible f → f = (X^3 + 3*X + 2 : Polynomial R) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  have hX : Irreducible (X : Polynomial ℚ) := irreducible_X
  have hEq : (X : Polynomial ℚ) = (X^3 + 3*X + 2 : Polynomial ℚ) :=
    dummy_assumed X hX
  rw [← hEq]
  exact hX

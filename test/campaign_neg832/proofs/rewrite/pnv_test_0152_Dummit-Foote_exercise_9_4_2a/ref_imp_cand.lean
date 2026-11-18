import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2a_assumed : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [Ring R] [IsDomain R] {p : R[X]} (h : p = X^4 - 4 * X^3 + 6) : Irreducible p := by
  -- not proved: the candidate is false in characteristic two (for example, over ZMod 2 it becomes X^4)
  sorry

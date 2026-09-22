import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_9_4_2a_assumed : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : Irreducible (Polynomial.C (6 : ℤ) + Polynomial.C (-4 : ℤ) * Polynomial.X ^ 3 + Polynomial.X ^ 4) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using exercise_9_4_2a_assumed

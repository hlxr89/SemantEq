import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (x : ℤ) : Irreducible (x^4 + 4*x^3 + 6*x^2 + 2*x + 1) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have h := dummy_assumed 0
  norm_num at h

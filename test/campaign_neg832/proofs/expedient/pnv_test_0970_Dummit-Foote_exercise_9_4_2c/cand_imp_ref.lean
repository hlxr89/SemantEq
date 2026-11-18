import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : Polynomial ℝ} : p = X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 → ¬(p = (a * X + b) * (c * X + d) ∧ a * c ≠ 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  exfalso
  have h := dummy_assumed
    (p := X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1)
    (a := 1) (b := X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 - X)
    (c := 1) (d := 1 - X) rfl
  apply h
  constructor
  · ring
  · norm_num

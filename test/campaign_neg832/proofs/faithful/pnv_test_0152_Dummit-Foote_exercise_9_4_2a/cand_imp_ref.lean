import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Ring R] [IsDomain R] {p : R[X]} (h : p = X^4 - 4 * X^3 + 6) : Irreducible p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  exact dummy_assumed (R := ℤ) (p := X^4 - 4*X^3 + 6) rfl

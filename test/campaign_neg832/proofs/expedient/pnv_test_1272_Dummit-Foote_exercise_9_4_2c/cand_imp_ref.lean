import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (p : ℤ[X]) (hp1 : p.degree = 4) (hp2 : p.eval (-1) = 1) (hp3 : p.eval 1 = 1) : Irreducible p := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2c : Irreducible
  (X^4 + 4*X^3 + 6*X^2 + 2*X + 1 : Polynomial ℤ) := by
  have h := dummy_assumed (X ^ 4) (by simp) (by norm_num) (by norm_num)
  rw [show (X ^ 4 : ℤ[X]) = X ^ 2 * X ^ 2 by ring] at h
  rcases h.2 rfl with h | h
  · have hd := Polynomial.degree_eq_zero_of_isUnit h
    simp at hd
  · have hd := Polynomial.degree_eq_zero_of_isUnit h
    simp at hd

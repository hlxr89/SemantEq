import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [Field R] (f : R[X]) (hf : f.degree = 3) (r : R) (hr : f.IsRoot r) : Irreducible f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  have hI : Irreducible ((X : Polynomial ℚ)^3) :=
    dummy_assumed ((X : Polynomial ℚ)^3) (by simp) 0 (by simp [Polynomial.IsRoot])
  exfalso
  rcases hI.isUnit_or_isUnit (show (X : Polynomial ℚ)^3 = X * X^2 by ring) with hX | hX2
  · exact (Polynomial.not_isUnit_of_natDegree_pos (X : Polynomial ℚ) (by simp)) hX
  · exact (Polynomial.not_isUnit_of_natDegree_pos ((X : Polynomial ℚ)^2) (by simp)) hX2

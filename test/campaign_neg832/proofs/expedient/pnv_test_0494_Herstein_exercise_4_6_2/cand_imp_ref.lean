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
  exfalso
  apply not_irreducible_pow (x := (X : Polynomial ℚ)) (n := 3) (by norm_num)
  apply dummy_assumed (X ^ 3) (by simp) 0
  simp [IsRoot]

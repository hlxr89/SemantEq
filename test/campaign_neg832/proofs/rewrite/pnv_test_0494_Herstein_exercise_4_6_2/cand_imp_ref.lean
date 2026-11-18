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
  -- not proved: applying the assumed statement would require a rational root, but this polynomial has none
  sorry

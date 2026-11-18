import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_6_2_assumed : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {R : Type*} [Field R] (f : R[X]) (hf : f.degree = 3) (r : R) (hr : f.IsRoot r) : Irreducible f := by
  -- not proved: the candidate is false (for example, X^3 has degree 3 and root 0 but is reducible)
  sorry

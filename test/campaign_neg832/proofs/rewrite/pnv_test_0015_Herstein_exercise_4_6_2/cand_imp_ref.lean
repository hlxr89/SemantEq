import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {n : ℕ} (hn : 0 < n) (a b : ℕ) (h : a * b = n) (ha : Irreducible a) (hb : Irreducible b) : Irreducible n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_6_2 : Irreducible (X^3 + 3*X + 2 : Polynomial ℚ) := by
  -- not proved: no rewrite transport relates the false natural-number claim to this polynomial claim
  sorry

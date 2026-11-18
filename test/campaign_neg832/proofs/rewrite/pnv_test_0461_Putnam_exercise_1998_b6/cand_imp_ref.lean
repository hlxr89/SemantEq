import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a b c : ℤ) (h : ∃ n : ℤ, (n : ℝ)^3 + (a * n^2) + (b * n) + c ≠ (n : ℝ)) : ∃ n : ℤ, 0 < n ∧ (n : ℝ)^3 + (a * n^2) + (b * n) + c ≠ (n : ℝ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1998_b6 (a b c : ℤ) :
  ∃ n : ℤ, n > 0 ∧ ¬ ∃ m : ℤ, Real.sqrt (n^3 + a*n^2 + b*n + c) = m := by
  -- not proved: the assumed statement only transports a non-fixed point to a positive non-fixed point; it gives no point whose value is not an integer square
  sorry

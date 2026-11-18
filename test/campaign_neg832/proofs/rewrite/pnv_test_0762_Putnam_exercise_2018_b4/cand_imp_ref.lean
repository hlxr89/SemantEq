import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} (x : ℕ → ℝ) (hx0 : x 0 = 1) (hx1 : x 1 = a) (hx2 : x 2 = a) (hx : ∀ n : ℕ, n ≥ 2 → x (n+2) = 2*x n*x (n+1) - x (n-2)) (hxn0 : ∃ n : ℕ, x n = 0) : ∃ p : ℕ, p > 0 ∧ ∀ n : ℕ, x (n % p) = x n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  -- not proved: the reference recurrence is not a re-expression of the candidate recurrence
  sorry

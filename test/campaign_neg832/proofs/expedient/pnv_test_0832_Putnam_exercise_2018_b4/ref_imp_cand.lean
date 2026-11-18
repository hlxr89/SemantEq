import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2018_b4_assumed (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {a : ℝ} {n : ℕ} (h : a ^ 2 = 2 * a - 1) (H : (2 ^ n + 1) * a ^ (n + 1) = 2 * a) : ∃ m : ℕ, ∀ k ≥ m, (2 ^ k + 1) * a ^ (k + 1) = 2 * a := by
  -- not proved: the candidate statement is false at a = 1 and n = 0, while the reference statement is consistent
  sorry

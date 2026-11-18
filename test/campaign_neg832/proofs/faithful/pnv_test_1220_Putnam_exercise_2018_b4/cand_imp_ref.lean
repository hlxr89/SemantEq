import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} {x : ℕ → ℝ} (hx : x 0 = 1) (hx' : x 1 = x 2) (hx'' : x 2 = a) (hnz : ∃ n : ℕ, x n = 0) : ∃ p : ℕ, ∀ i : ℕ, x (i + p) = x i := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  -- not proved: the assumed statement may witness its unrestricted period with zero
  sorry

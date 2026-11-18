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
theorem dummy (a : ℝ) (x : ℕ → ℝ) (h0 : x 0 = 1) (h1 : x 1 = a) (h2 : x 2 = a) (h_rec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (h_zero : ∃ n, x n = 0) : ∃ p, ∀ k, x (k + p) = x k := by
  obtain ⟨p, hp, hper⟩ := exercise_2018_b4_assumed a x h0 h1 h2 h_rec h_zero
  exact ⟨p, hper⟩

import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} : ∃ (x : ℕ → ℝ), x 0 = 1 ∧ x 1 = a ∧ x 2 = a ∧ (∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) ∧ (∃ n : ℕ, x n = 0 ∧ ∀ m : ℕ, x (n + m) = x m) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  obtain ⟨y, hy0, _, _, _, n, hn0, hnper⟩ := dummy_assumed (a := a)
  have hbad := hnper 0
  simp [hn0, hy0] at hbad

import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (ha : a > 0) (hn : a ^ n = 1): ∃ m, a ^ (m + 1) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  exfalso
  obtain ⟨m, hm⟩ := dummy_assumed (a := 2) (n := 0) (by norm_num) (by norm_num)
  have hm_gt : 1 < 2 ^ (m + 1) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  omega

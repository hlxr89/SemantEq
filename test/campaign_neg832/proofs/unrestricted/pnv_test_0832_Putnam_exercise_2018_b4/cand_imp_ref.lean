import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} {n : ℕ} (h : a ^ 2 = 2 * a - 1) (H : (2 ^ n + 1) * a ^ (n + 1) = 2 * a) : ∃ m : ℕ, ∀ k ≥ m, (2 ^ k + 1) * a ^ (k + 1) = 2 * a := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  obtain ⟨m, hm⟩ := dummy_assumed (a := (1 : ℝ)) (n := 0) (by norm_num) (by norm_num)
  have hbad := hm (m + 1) (by omega)
  norm_num [pow_succ] at hbad
  have hpow_aux : ∀ j : ℕ, (1 : ℝ) ≤ 2 ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      nlinarith
  have hpow := hpow_aux m
  nlinarith

import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a : ℝ} (x : ℕ → ℝ) (h0 : x 0 = 1) (h1 : x 1 = a) (h2 : x 2 = a) (h_rec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (n : ℕ) (hn : x n = 0) : ∃ p > 0, ∀ m, x (m + p) = x m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨p, hp, hperiodic⟩ :=
    dummy_assumed (a := a) x hx0 hx1 hx2 hxn n hn
  exact ⟨p, Nat.ne_of_gt hp, hperiodic⟩

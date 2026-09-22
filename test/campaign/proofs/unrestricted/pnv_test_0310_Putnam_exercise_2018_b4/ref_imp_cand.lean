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
theorem dummy {a : ℝ} (x : ℕ → ℝ) (h0 : x 0 = 1) (h1 : x 1 = a) (h2 : x 2 = a) (h_rec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (n : ℕ) (hn : x n = 0) : ∃ p > 0, ∀ m, x (m + p) = x m := by
  obtain ⟨p, hp_ne, hp_periodic⟩ :=
    exercise_2018_b4_assumed a x h0 h1 h2 h_rec ⟨n, hn⟩
  exact ⟨p, Nat.pos_of_ne_zero hp_ne, hp_periodic⟩

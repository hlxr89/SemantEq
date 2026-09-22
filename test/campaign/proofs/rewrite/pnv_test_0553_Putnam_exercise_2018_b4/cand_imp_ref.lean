import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (x : ℕ → ℝ) (hx1 : x 0 = 1) (hx2 : x 1 = x 2) (hx : ∀ n : ℕ, n ≥ 2 → x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (hn : ∃ n : ℕ, x n = 0) : ∃ n : ℕ, n ≠ 0 ∧ ∀ m : ℕ, x (n + m) = x m := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2018_b4 (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1)
  (hx1 : x 1 = a) (hx2 : x 2 = a)
  (hxn : ∀ n : ℕ, n ≥ 2 → x (n+1) = 2*(x n)*(x (n-1)) - x (n-2))
  (h : ∃ n, x n = 0) :
  ∃ c ≠ 0, Function.Periodic x c := by
  obtain ⟨n, hn0, hperiodic⟩ :=
    dummy_assumed x hx0 (hx1.trans hx2.symm) hxn h
  refine ⟨n, hn0, ?_⟩
  intro m
  rw [Nat.add_comm]
  exact hperiodic m

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
theorem dummy {a : ℝ} {x : ℕ → ℝ} (hx0 : x 0 = 1) (hx1 : x 1 = a) (hx2 : x 2 = a) (hx : ∀ (n : ℕ), n + 2 > 0 → x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (hx0_eq_0 : ∃ n, x n = 0) : ∃ k, ∀ m, n ≥ k → x m = x n := by
  obtain ⟨c, hc, _⟩ := exercise_2018_b4_assumed a x hx0 hx1 hx2
    (fun n _ ↦ hx n (Nat.zero_lt_succ _)) hx0_eq_0
  refine ⟨n + c, ?_⟩
  intro m hnc
  have hlt : n < n + c := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hc)
  exact (Nat.not_lt_of_ge hnc hlt).elim -- non-rewrite step

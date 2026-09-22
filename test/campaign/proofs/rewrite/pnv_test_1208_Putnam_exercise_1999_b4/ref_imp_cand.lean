import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1999_b4_assumed (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} (h_cont : ∀ n ≤ 3, Continuous (deriv^[n] f)) (h_pos : ∀ x, (∀ n ≤ 3, (deriv^[n] f) x > 0)) (h_bound : ∀ x, (deriv^[3] f) x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  apply exercise_1999_b4_assumed f
  · apply contDiff_nat_iff_iteratedDeriv.mpr
    constructor
    · intro n hn
      rw [iteratedDeriv_eq_iterate]
      exact h_cont n hn
    · intro n hn
      intro x
      apply differentiableAt_of_deriv_ne_zero -- non-rewrite step
      rw [← iteratedDeriv_succ, iteratedDeriv_eq_iterate]
      exact ne_of_gt (h_pos x (n + 1) hn)
  · intro n hn x
    rw [iteratedDeriv_eq_iterate]
    exact h_pos x n hn
  · intro x
    rw [iteratedDeriv_eq_iterate]
    exact h_bound x

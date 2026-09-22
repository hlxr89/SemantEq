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
  have hf : ContDiff ℝ 3 f := by
    apply contDiff_iff_iteratedDeriv.mpr
    constructor
    · intro n hn
      rw [iteratedDeriv_eq_iterate]
      exact h_cont n (by exact_mod_cast hn)
    · intro n hn
      intro x
      apply differentiableAt_of_deriv_ne_zero
      have hp : iteratedDeriv (n + 1) f x > 0 := by
        rw [iteratedDeriv_eq_iterate]
        exact h_pos x (n + 1) (by exact_mod_cast hn)
      rw [iteratedDeriv_succ] at hp
      exact ne_of_gt hp
  apply exercise_1999_b4_assumed f hf
  · intro n hn x
    rw [iteratedDeriv_eq_iterate]
    exact h_pos x n hn
  · intro x
    rw [iteratedDeriv_eq_iterate]
    exact h_bound x

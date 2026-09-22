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
theorem dummy {f : ℝ → ℝ} (h_cont : ∀ n ≤ 3, Continuous (deriv^[n] f)) (h_pos : ∀ x, 0 < f x ∧ 0 < deriv f x ∧ 0 < deriv^[2] f x ∧ 0 < deriv^[3] f x) (h_ineq : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  apply exercise_1999_b4_assumed f
  · apply contDiff_iff_iteratedDeriv.2
    constructor
    · intro n hn
      rw [iteratedDeriv_eq_iterate]
      exact h_cont n (by exact_mod_cast hn)
    · intro n hn x
      apply differentiableAt_of_deriv_ne_zero
      rw [← iteratedDeriv_succ]
      have hn' : n < 3 := by exact_mod_cast hn
      rw [iteratedDeriv_eq_iterate]
      interval_cases n
      · exact (h_pos x).2.1.ne'
      · exact (h_pos x).2.2.1.ne'
      · exact (h_pos x).2.2.2.ne'
  · intro n hn x
    rw [iteratedDeriv_eq_iterate]
    interval_cases n
    · exact (h_pos x).1
    · exact (h_pos x).2.1
    · exact (h_pos x).2.2.1
    · exact (h_pos x).2.2.2
  · simpa [iteratedDeriv_eq_iterate] using h_ineq

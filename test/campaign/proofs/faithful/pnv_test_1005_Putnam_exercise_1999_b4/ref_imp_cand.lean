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
  have h_pos' : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0 := by
    intro n hn x
    interval_cases n
    · simpa [iteratedDeriv_eq_iterate] using (h_pos x).1
    · simpa [iteratedDeriv_eq_iterate] using (h_pos x).2.1
    · simpa [iteratedDeriv_eq_iterate] using (h_pos x).2.2.1
    · simpa [iteratedDeriv_eq_iterate] using (h_pos x).2.2.2
  apply exercise_1999_b4_assumed f
  · refine (contDiff_nat_iff_iteratedDeriv (f := f) (n := 3)).2 ?_
    constructor
    · intro n hn
      simpa only [iteratedDeriv_eq_iterate] using h_cont n hn
    · intro n hn x
      apply differentiableAt_of_deriv_ne_zero
      rw [← iteratedDeriv_succ]
      exact ne_of_gt (h_pos' (n + 1) (by omega) x)
  · exact h_pos'
  · simpa only [iteratedDeriv_eq_iterate] using h_ineq

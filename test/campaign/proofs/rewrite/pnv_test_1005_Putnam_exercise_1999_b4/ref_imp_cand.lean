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
  · change ContDiff ℝ (↑(3 : ℕ) : WithTop ℕ∞) f
    rw [contDiff_nat_iff_iteratedDeriv]
    constructor
    · intro n hn
      rw [iteratedDeriv_eq_iterate]
      exact h_cont n hn
    · intro n hn x
      apply differentiableAt_of_deriv_ne_zero
      rw [iteratedDeriv_eq_iterate]
      obtain ⟨h0, h1, h2, h3⟩ := h_pos x
      interval_cases n <;> simp only [Function.iterate_zero_apply,
        Function.iterate_succ_apply'] at * <;> exact ne_of_gt (by assumption)
  · intro n hn x
    rw [iteratedDeriv_eq_iterate]
    obtain ⟨h0, h1, h2, h3⟩ := h_pos x
    interval_cases n <;> simp only [Function.iterate_zero_apply,
      Function.iterate_succ_apply'] at * <;> assumption
  · intro x
    rw [iteratedDeriv_eq_iterate]
    exact h_ineq x

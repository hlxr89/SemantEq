import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf_pos : ∀ x, 0 < f x) (hf_cont : Continuous f) (hf_deriv_pos : ∀ x, 0 < deriv f x) (hf_deriv2_pos : ∀ x, 0 < deriv^[2] f x) (hf_deriv3_pos : ∀ x, 0 < deriv^[3] f x) (hf_deriv3_le_fun : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  apply dummy_assumed
  · intro x
    simpa [iteratedDeriv_zero] using hf1 0 (by omega) x
  · exact hf.continuous
  · intro x
    simpa [iteratedDeriv_succ] using hf1 1 (by omega) x
  · intro x
    simpa [iteratedDeriv_succ, Function.iterate_succ_apply'] using hf1 2 (by omega) x
  · intro x
    simpa [iteratedDeriv_succ, Function.iterate_succ_apply'] using hf1 3 (by omega) x
  · intro x
    simpa [iteratedDeriv_succ, Function.iterate_succ_apply'] using hf2 x

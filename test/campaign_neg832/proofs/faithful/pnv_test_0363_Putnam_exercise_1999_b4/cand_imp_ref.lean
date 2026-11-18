import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf_th : Continuous (deriv^[3] f)) (hf_pos : ∀ x, 0 < f x) (hf_deriv_pos : ∀ x, 0 < deriv f x) (hf_deriv_two_pos : ∀ x, 0 < deriv^[2] f x) (h : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  apply dummy_assumed
  · simpa only [← iteratedDeriv_eq_iterate] using
      hf.continuous_iteratedDeriv 3 (by norm_num)
  · simpa using hf1 0 (by norm_num)
  · simpa [iteratedDeriv_succ] using hf1 1 (by norm_num)
  · simpa only [← iteratedDeriv_eq_iterate] using hf1 2 (by norm_num)
  · simpa only [← iteratedDeriv_eq_iterate] using hf2

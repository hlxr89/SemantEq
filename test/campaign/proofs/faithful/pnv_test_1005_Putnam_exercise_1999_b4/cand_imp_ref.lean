import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h_cont : ∀ n ≤ 3, Continuous (deriv^[n] f)) (h_pos : ∀ x, 0 < f x ∧ 0 < deriv f x ∧ 0 < deriv^[2] f x ∧ 0 < deriv^[3] f x) (h_ineq : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  apply dummy_assumed (f := f)
  · intro n hn
    have hc := (contDiff_nat_iff_iteratedDeriv.mp hf).1 n hn
    simpa only [iteratedDeriv_eq_iterate] using hc
  · intro x
    constructor
    · simpa [iteratedDeriv_eq_iterate] using hf1 0 (by omega) x
    constructor
    · simpa [iteratedDeriv_eq_iterate] using hf1 1 (by omega) x
    constructor
    · simpa [iteratedDeriv_eq_iterate] using hf1 2 (by omega) x
    · simpa [iteratedDeriv_eq_iterate] using hf1 3 (by omega) x
  · simpa only [iteratedDeriv_eq_iterate] using hf2

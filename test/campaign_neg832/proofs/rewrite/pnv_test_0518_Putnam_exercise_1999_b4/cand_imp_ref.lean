import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ x, 0 < f x) (hf' : ∀ x, 0 < deriv f x) (hf'' : ∀ x, 0 < deriv^[2] f x) (hf''' : ∀ x, 0 < deriv^[3] f x) (h_bound : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  apply dummy_assumed
  · intro x
    exact hf1 0 (Nat.zero_le 3) x
  · intro x
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hf1 1 (Nat.succ_le_succ (Nat.zero_le 2)) x
  · intro x
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hf1 2 (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) x
  · intro x
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hf1 3 le_rfl x
  · intro x
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hf2 x

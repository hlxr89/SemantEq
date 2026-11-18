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
  apply dummy_assumed (f := f)
  · intro x
    simpa only [iteratedDeriv_zero] using hf1 0 (Nat.zero_le 3) x
  · exact hf.continuous
  · intro x
    have h := hf1 1 (Nat.succ_le_succ (Nat.zero_le 2)) x
    rw [iteratedDeriv_eq_iterate] at h
    exact h
  · intro x
    have h := hf1 2 (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) x
    rw [iteratedDeriv_eq_iterate] at h
    exact h
  · intro x
    have h := hf1 3 le_rfl x
    rw [iteratedDeriv_eq_iterate] at h
    exact h
  · intro x
    have h := hf2 x
    rw [iteratedDeriv_eq_iterate] at h
    exact h

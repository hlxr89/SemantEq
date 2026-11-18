import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (hf' : ∀ x, 0 < deriv f x) (hf'' : Continuous (deriv^[2] f)) (hf''' : ∀ x, deriv^[3] f x ≤ f x) : ∀ x, (deriv f) x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  apply dummy_assumed
  · intro x
    exact le_of_lt (by simpa only [iteratedDeriv_zero] using hf1 0 (Nat.zero_le 3) x)
  · intro x
    rw [← iteratedDeriv_one]
    exact hf1 1 (Nat.succ_le_succ (Nat.zero_le 2)) x
  · rw [← iteratedDeriv_eq_iterate]
    exact hf.continuous_iteratedDeriv 2 (by exact_mod_cast Nat.le_succ 2)
  · intro x
    rw [← iteratedDeriv_eq_iterate]
    exact hf2 x

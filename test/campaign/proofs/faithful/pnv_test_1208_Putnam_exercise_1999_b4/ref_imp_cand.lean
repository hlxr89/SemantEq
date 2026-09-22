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
  intro x
  apply exercise_1999_b4_assumed f
  · change ContDiff ℝ (↑(3 : ℕ∞)) f
    rw [contDiff_iff_iteratedDeriv]
    constructor
    · intro n hn
      rw [iteratedDeriv_eq_iterate]
      apply h_cont n
      exact_mod_cast hn
    · intro n hn y
      apply differentiableAt_of_deriv_ne_zero
      rw [← iteratedDeriv_succ, iteratedDeriv_eq_iterate]
      have hn' : n + 1 ≤ 3 := by
        apply Nat.succ_le_iff.mpr
        exact_mod_cast hn
      exact ne_of_gt (h_pos y (n + 1) hn')
  · intro n hn y
    rw [iteratedDeriv_eq_iterate]
    exact h_pos y n hn
  · intro y
    rw [iteratedDeriv_eq_iterate]
    exact h_bound y

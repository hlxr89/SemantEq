import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h_cont : ∀ n ≤ 3, Continuous (deriv^[n] f)) (h_pos : ∀ x, (∀ n ≤ 3, (deriv^[n] f) x > 0)) (h_bound : ∀ x, (deriv^[3] f) x ≤ f x) : ∀ x, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  intro x
  apply dummy_assumed
  · intro n hn
    rw [← iteratedDeriv_eq_iterate]
    apply (contDiff_iff_iteratedDeriv.mp hf).1 n
    exact_mod_cast hn
  · intro y n hn
    rw [← iteratedDeriv_eq_iterate]
    exact hf1 n hn y
  · intro y
    rw [← iteratedDeriv_eq_iterate]
    exact hf2 y

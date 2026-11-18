import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ x : ℝ, HasDerivAt f (deriv f x) x) (hdf : ∀ x : ℝ, HasDerivAt (deriv f) (deriv (deriv f) x) x) (hg : ∀ x : ℝ, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x) (hgf : ∀ x : ℝ, (deriv f x) > 0) (hg2f : ∀ x : ℝ, (deriv (deriv f) x) > 0) (hg2gf : ∀ x : ℝ, (deriv (deriv (deriv f)) x) ≤ (deriv f x)) : ∀ x : ℝ, deriv f x < 2 * f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1999_b4 (f : ℝ → ℝ) (hf: ContDiff ℝ 3 f)
  (hf1 : ∀ n ≤ 3, ∀ x : ℝ, iteratedDeriv n f x > 0)
  (hf2 : ∀ x : ℝ, iteratedDeriv 3 f x ≤ f x) :
  ∀ x : ℝ, deriv f x < 2 * f x := by
  -- not proved: the ref bound on the third derivative is by f, while the candidate requires a bound by deriv f
  sorry

import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b : ℤ} (hab : a ∣ b) : a ∣ b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  intro h
  rcases h with ⟨z, hz⟩
  have hab : a ∣ b := by
    refine ⟨z.re, ?_⟩
    -- non-rewrite step: project the supplied Gaussian divisibility witness to its real part.
    simpa only [Zsqrtd.re_ofInt, Zsqrtd.re_mul, Zsqrtd.im_ofInt, mul_zero,
      zero_mul, add_zero] using congrArg Zsqrtd.re hz
  exact dummy_assumed hab

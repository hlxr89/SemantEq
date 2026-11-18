import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a b : ℤ} (h : a ∣ b) : a ∣ b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_11_2_13 (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  rintro ⟨z, hz⟩
  refine ⟨z.re, ?_⟩
  simpa using congrArg Zsqrtd.re hz

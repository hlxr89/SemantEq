import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_11_2_13_assumed (a b : ℤ) :
  (ofInt a : GaussianInt) ∣ ofInt b → a ∣ b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (a b : ℤ) (ha : a ∣ b) : a ∣ (b : ℤ) := by
  exact exercise_11_2_13_assumed a b (by
    rcases ha with ⟨c, rfl⟩
    exact ⟨ofInt c, by simp⟩)

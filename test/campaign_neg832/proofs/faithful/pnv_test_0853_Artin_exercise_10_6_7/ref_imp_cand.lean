import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_10_6_7_assumed {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (I : Ideal (GaussianInt)) (hI : I ≠ 0) : ∃ z : GaussianInt, z ≠ 0 ∧ z ∈ I := by
  obtain ⟨z, hz, _⟩ := exercise_10_6_7_assumed (I := I) hI
  exact ⟨z, by simpa using hz, z.property⟩

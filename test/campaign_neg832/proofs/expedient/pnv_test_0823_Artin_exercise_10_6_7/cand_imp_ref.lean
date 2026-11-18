import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (I : Ideal (GaussianInt)) (hI : I ≠ 0) : ∃ x : GaussianInt, x ≠ 0 ∧ x ∈ I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  obtain ⟨x, hx, hxI⟩ := dummy_assumed I hI
  refine ⟨⟨x * star x, I.mul_mem_right (star x) hxI⟩, ?_, ?_⟩
  · simpa [mul_eq_zero] using hx
  · simp [Zsqrtd.im_mul]
    ring

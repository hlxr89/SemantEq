import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {I : Ideal ℤ} (hI : I ≠ ⊥) : ∃ (n : ℤ), n ≠ 0 ∧ n ∈ I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  obtain ⟨w, hwI, hw0⟩ := I.ne_bot_iff.mp hI
  have hmem : w * star w ∈ I := I.mul_mem_right (star w) hwI
  refine ⟨⟨w * star w, hmem⟩, ?_, ?_⟩
  · intro h
    have hval : w * star w = 0 := congrArg Subtype.val h
    exact (mul_ne_zero hw0 (by simpa using hw0)) hval
  · change (w * star w).im = 0
    simp [Zsqrtd.im_mul]
    ring

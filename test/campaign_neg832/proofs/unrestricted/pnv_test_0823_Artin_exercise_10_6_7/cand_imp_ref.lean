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
  let y : GaussianInt := ⟨x.re, -x.im⟩
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    apply Zsqrtd.ext
    · have hre := congrArg Zsqrtd.re hy0
      simpa [y] using hre
    · have him := congrArg Zsqrtd.im hy0
      simp [y] at him
      exact him
  let z : I := ⟨x * y, I.mul_mem_right y hxI⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    have hxy : x * y = 0 := congrArg Subtype.val hz
    exact (mul_ne_zero hx hy) hxy
  · change (x * y).im = 0
    rw [Zsqrtd.im_mul]
    dsimp [y]
    ring

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
  have hnorm : x.norm ≠ 0 := GaussianInt.norm_eq_zero.not.mpr hx
  let z : I := ⟨(x.norm : GaussianInt), by
    rw [Zsqrtd.norm_eq_mul_conj]
    exact I.mul_mem_right (star x) hxI⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    apply hnorm
    have hz' : (x.norm : GaussianInt) = 0 := by
      simpa [z] using congr_arg Subtype.val hz
    exact_mod_cast hz'
  · simp [z]

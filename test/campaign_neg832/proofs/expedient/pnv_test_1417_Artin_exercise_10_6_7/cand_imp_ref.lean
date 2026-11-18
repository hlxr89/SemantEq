import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [Ring R] (I : Ideal R) (hI : I ≠ 0) : ∃ x : R, x ≠ 0 ∧ x ∈ I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_10_6_7 {I : Ideal GaussianInt}
  (hI : I ≠ ⊥) : ∃ (z : I), z ≠ 0 ∧ (z : GaussianInt).im = 0 := by
  rcases dummy_assumed I hI with ⟨w, hw0, hwI⟩
  let c : GaussianInt := ⟨w.re, -w.im⟩
  have hc : c ≠ 0 := by
    intro hc0
    apply hw0
    apply Zsqrtd.ext
    · simpa [c] using congrArg Zsqrtd.re hc0
    · have h := congrArg Zsqrtd.im hc0
      simp [c] at h
      exact h
  let z : I := ⟨c * w, I.mul_mem_left c hwI⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    exact (mul_ne_zero hc hw0) (congrArg Subtype.val hz)
  · simp [z, c, Zsqrtd.im_mul]
    ring

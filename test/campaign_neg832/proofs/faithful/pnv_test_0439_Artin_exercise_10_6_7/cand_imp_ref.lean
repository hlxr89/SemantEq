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
  let J : Ideal ℤ := I.comap (algebraMap ℤ GaussianInt)
  have hJ : J ≠ ⊥ := by
    rw [Submodule.ne_bot_iff] at hI ⊢
    obtain ⟨z, hzI, hz0⟩ := hI
    refine ⟨z.norm, ?_, ?_⟩
    · change (z.norm : GaussianInt) ∈ I
      rw [Zsqrtd.norm_eq_mul_conj]
      exact I.mul_mem_right _ hzI
    · exact (GaussianInt.norm_eq_zero.not).2 hz0
  obtain ⟨n, hn0, hnJ⟩ := dummy_assumed hJ
  refine ⟨⟨(n : GaussianInt), hnJ⟩, ?_, ?_⟩
  · intro hn
    have : (n : GaussianInt) = 0 := congrArg Subtype.val hn
    exact hn0 (Int.cast_injective this)
  · simp

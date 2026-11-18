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
  obtain ⟨z, hz0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  let f : ℤ →+* GaussianInt := algebraMap ℤ GaussianInt
  have hnorm_mem : (z.1.norm : GaussianInt) ∈ I := by
    rw [Zsqrtd.norm_eq_mul_conj]
    exact I.mul_mem_right (star z.1) z.2
  have hnorm0 : z.1.norm ≠ 0 := by
    intro hnorm
    apply hz0
    apply Subtype.ext
    exact GaussianInt.norm_eq_zero.mp hnorm
  have hcomap : Ideal.comap f I ≠ ⊥ := by
    intro hbot
    apply hnorm0
    exact Ideal.mem_bot.mp (hbot ▸ (show z.1.norm ∈ Ideal.comap f I from hnorm_mem))
  obtain ⟨n, hn0, hnmem⟩ := dummy_assumed hcomap
  refine ⟨⟨(n : GaussianInt), hnmem⟩, ?_, ?_⟩
  · intro hn
    apply hn0
    exact Int.cast_injective (congr_arg Subtype.val hn)
  · exact Zsqrtd.im_intCast n

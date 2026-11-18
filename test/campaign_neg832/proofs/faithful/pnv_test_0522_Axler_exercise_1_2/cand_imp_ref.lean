import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : 1 = Real.cos (π / 3) + Real.sin (π / 3) * Complex.I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_2 :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  have hroot :
      (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) =
        (Real.cos (Real.pi / 3) + Real.sin (Real.pi / 3) * Complex.I) ^ 2 := by
    rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
    apply Complex.ext <;>
      norm_num [pow_two, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hroot, ← dummy_assumed]
  norm_num

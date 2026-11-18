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
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 3 ^ 2 = 3 := by simpa [pow_two] using hs
  apply Complex.ext <;>
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im] <;>
    ring_nf
  · rw [hs2]
    norm_num
  · rw [show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [pow_succ, hs2]]
    ring

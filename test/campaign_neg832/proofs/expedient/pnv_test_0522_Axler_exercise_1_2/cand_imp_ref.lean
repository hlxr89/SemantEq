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
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Complex.ext_iff]
  constructor
  · norm_num [pow_succ]
    nlinarith [hs]
  · norm_num [pow_succ]
    ring_nf
    rw [show (Real.sqrt 3) ^ 3 = Real.sqrt 3 * 3 by rw [pow_succ, hs]; ring]
    ring

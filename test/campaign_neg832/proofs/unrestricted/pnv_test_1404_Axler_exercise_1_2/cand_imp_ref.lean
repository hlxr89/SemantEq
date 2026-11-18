import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : (((-1 + 3 * i) / 2) ^ 3 : ℂ) = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_2 :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  apply Complex.ext <;> norm_num [pow_succ]
  · nlinarith
  · ring_nf
    rw [show (Real.sqrt 3) ^ 3 = Real.sqrt 3 * (Real.sqrt 3) ^ 2 by ring, hs]
    ring

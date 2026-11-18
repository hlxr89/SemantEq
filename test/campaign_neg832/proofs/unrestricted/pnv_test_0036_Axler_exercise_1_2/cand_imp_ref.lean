import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : 1 = Complex.cos (π / 3) + Complex.sin (π / 3) * Complex.I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_2 :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hc : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs]
  apply Complex.ext <;> norm_num [pow_succ]
  · nlinarith [hs]
  · nlinarith [hs, hc]

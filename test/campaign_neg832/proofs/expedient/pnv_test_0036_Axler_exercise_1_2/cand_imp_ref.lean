import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : 1 = Complex.cos (π / 3) + Complex.sin (π / 3) * Complex.I := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_2 :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  apply Complex.ext <;> norm_num [pow_succ]
  all_goals ring_nf
  all_goals
    nlinarith [hs, congrArg (fun x : ℝ => x * Real.sqrt 3) hs]

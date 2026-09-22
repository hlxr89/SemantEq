import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_3_9_assumed : ∫ x in (0 : ℝ)..(1 : ℝ), Real.log (Real.sin (Real.pi * x)) = - Real.log 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_3_9_alt :
    ∫ x in Set.Ioc (0 : ℝ) (1 : ℝ), Real.log (Real.sin (Real.pi * x)) = - Real.log 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  exact exercise_3_9_assumed

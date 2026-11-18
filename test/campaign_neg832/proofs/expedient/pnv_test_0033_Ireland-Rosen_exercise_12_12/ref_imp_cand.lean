import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_12_12_assumed : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : IsAlgebraic ℝ ((π / 12) : ℝ) := by
  simpa using (isAlgebraic_algebraMap (R := ℝ) (A := ℝ) (π / 12))

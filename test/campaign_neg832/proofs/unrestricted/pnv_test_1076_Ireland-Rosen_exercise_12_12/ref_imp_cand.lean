import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

-- ===== assumed statement (antecedent) =====
theorem exercise_12_12_assumed : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : IsAlgebraic ℝ (Real.sin (π / 12)) := by
  simpa using
    (isAlgebraic_algebraMap (R := ℝ) (A := ℝ) (Real.sin (π / 12)))

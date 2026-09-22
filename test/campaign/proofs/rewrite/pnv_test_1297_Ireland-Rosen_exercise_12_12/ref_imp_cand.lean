import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_12_12_assumed : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : IsAlgebraic ℤ (sin (π / 12)) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ]
  exact exercise_12_12_assumed

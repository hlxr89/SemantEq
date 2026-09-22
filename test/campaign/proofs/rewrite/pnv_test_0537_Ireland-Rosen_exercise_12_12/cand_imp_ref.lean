import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : IsAlgebraic ℚ (Real.sin (π / 12)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_12_12 : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  exact dummy_assumed

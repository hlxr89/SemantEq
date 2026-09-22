import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_12_12_assumed : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : IsAlgebraic ℤ (sin (π/12)) := by
  simpa [div_eq_mul_inv, mul_comm] using isAlgebraic_sin_rat_mul_pi (1 / 12 : ℚ)

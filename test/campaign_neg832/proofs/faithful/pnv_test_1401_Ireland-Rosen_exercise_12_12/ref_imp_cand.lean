import Mathlib

open Real
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_12_12_assumed : IsAlgebraic ℚ (sin (Real.pi/12)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : IsAlgebraic ℝ (sin (π / 12)) := by
  rcases exercise_12_12_assumed with ⟨p, hp, hroot⟩
  refine ⟨p.map (algebraMap ℚ ℝ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).2 hp
  · simpa [Polynomial.aeval_def] using hroot

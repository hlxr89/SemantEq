import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_1_2_assumed :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : (Complex.mk (-1 / 2) (Real.sqrt 3 / 2)) ^ 3 = 1 := by
  simpa using exercise_1_2_assumed

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [CommRing R] {u : R} (hu : IsUnit u) : IsUnit (-u) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u) := by
  have hneg1Z : IsUnit (-(1 : ℤ)) := dummy_assumed isUnit_one
  have hneg1R : IsUnit (-(1 : R)) := by
    simpa using hneg1Z.map (Int.castRingHom R)
  simpa only [neg_one_mul] using hneg1R.mul hu

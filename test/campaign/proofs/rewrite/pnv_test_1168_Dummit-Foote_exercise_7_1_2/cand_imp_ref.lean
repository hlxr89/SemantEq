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
  have hnegInt : IsUnit (-(1 : ℤ)) := dummy_assumed isUnit_one
  have hnegOne : IsUnit (-(1 : R)) := by
    simpa only [map_neg, map_one] using hnegInt.map (Int.castRingHom R)
  rw [← neg_one_mul u]
  exact hnegOne.mul hu

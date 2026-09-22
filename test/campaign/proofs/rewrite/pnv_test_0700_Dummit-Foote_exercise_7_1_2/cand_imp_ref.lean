import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] (u : R) (hu : IsUnit u) : IsUnit (-u) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u) := by
  have hneg_one_int : IsUnit (-(1 : ℤ)) := dummy_assumed 1 isUnit_one
  have hneg_one : IsUnit (-(1 : R)) := by
    simpa only [map_neg, map_one] using hneg_one_int.map (Int.castRingHom R)
  simpa only [neg_mul, one_mul] using hneg_one.mul hu

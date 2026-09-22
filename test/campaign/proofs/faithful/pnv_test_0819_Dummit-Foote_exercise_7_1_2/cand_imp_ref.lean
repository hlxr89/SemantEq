import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (R : Type*) [CommRing R] (u : R) (hu : IsUnit u) : IsUnit (-u) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_7_1_2 {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) : IsUnit (-u) := by
  have hnegOneZ : IsUnit (-(1 : ℤ)) := dummy_assumed ℤ 1 isUnit_one
  have hnegOneR : IsUnit ((-(1 : ℤ) : ℤ) : R) :=
    hnegOneZ.map (Int.castRingHom R)
  simpa using hnegOneR.mul hu

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [IsDomain ℤ] [CharZero ℤ] (h : IsIntegrallyClosed ℤ) : Irreducible (X^2 - sqrt₂ : ℤ[X]) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  exfalso
  have hirr : Irreducible ((X : ℤ[X]) ^ 2) := by
    simpa using (dummy_assumed (sqrt₂ := 0) (by infer_instance))
  have hu : IsUnit (X : ℤ[X]) ∨ IsUnit (X : ℤ[X]) :=
    hirr.isUnit_or_isUnit (by rw [pow_two])
  exact hu.elim Polynomial.not_isUnit_X Polynomial.not_isUnit_X

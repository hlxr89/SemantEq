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
  have hbad : Irreducible (X^2 - X^2 : ℤ[X]) :=
    dummy_assumed (sqrt₂ := X^2) (by infer_instance)
  exact (hbad.ne_zero (sub_self _)).elim

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (sqrt2 : R) (h_sqrt2 : sqrt2 * sqrt2 = 2) : Irreducible (X^2 - C sqrt2 : Polynomial R) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have h := dummy_assumed (R := ZMod 2) 0 (by decide)
  have hX : Irreducible ((X : Polynomial (ZMod 2)) ^ 2) := by
    simpa using h
  exact (not_irreducible_pow (x := (X : Polynomial (ZMod 2))) (by decide) hX).elim

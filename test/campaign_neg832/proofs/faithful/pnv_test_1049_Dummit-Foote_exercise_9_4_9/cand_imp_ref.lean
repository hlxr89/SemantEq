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
  letI : Zsqrtd.Nonsquare 2 := ⟨by
    intro n h
    have hn : n ≤ 2 := by nlinarith
    interval_cases n <;> norm_num at h⟩
  letI : IsDomain (Zsqrtd (↑(2 : ℕ))) := inferInstance
  refine Polynomial.Monic.irreducible_of_irreducible_map
    (Zsqrtd.toReal (d := 2) (by norm_num))
    (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2))
    (monic_X_pow_sub_C _ (by norm_num)) ?_
  simpa using dummy_assumed (Real.sqrt 2) (Real.mul_self_sqrt (by norm_num))

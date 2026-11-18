import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [CommRing α] [IsDomain α] [UniqueFactorizationMonoid α] (sqrt2 : α) (h : sqrt2 * sqrt2 = 2) : Irreducible (Polynomial.C sqrt2 * Polynomial.X ^ 2 - Polynomial.C 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  letI : Zsqrtd.Nonsquare 2 := ⟨by
    intro n h
    have hn : n ≤ 2 := by nlinarith
    interval_cases n <;> norm_num at h⟩
  let R := Zsqrtd (↑(2 : ℕ))
  letI : IsDomain R := Zsqrtd.instIsDomainCastInt (d := 2)
  let K := FractionRing R
  letI : Field K := by dsimp [K]; infer_instance
  let sqrt2 : K := algebraMap R K Zsqrtd.sqrtd
  have hsqrt2 : sqrt2 * sqrt2 = 2 := by
    change algebraMap R K Zsqrtd.sqrtd * algebraMap R K Zsqrtd.sqrtd = 2
    rw [← map_mul, Zsqrtd.dmuld]
    exact map_ofNat (algebraMap R K) 2
  have hi := dummy_assumed (α := K) sqrt2 hsqrt2
  have hprod : Irreducible (C sqrt2 * (X ^ 2 - C sqrt2) : Polynomial K) := by
    convert hi using 1
    simp [mul_sub, ← C_mul, hsqrt2]
  have hirrK : Irreducible (X ^ 2 - C sqrt2 : Polynomial K) := by
    rcases irreducible_mul_iff.mp hprod with hbad | hgood
    · have hdegree := degree_eq_zero_of_isUnit hbad.2
      rw [degree_X_pow_sub_C (by norm_num)] at hdegree
      simp at hdegree
    · exact hgood.1
  let p : Polynomial R := X ^ 2 - C Zsqrtd.sqrtd
  have hpmap : Irreducible (p.map (algebraMap R K)) := by
    change Irreducible ((X ^ 2 - C Zsqrtd.sqrtd : Polynomial R).map (algebraMap R K))
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact hirrK
  have hpmonic : p.Monic := by
    exact monic_X_pow_sub_C Zsqrtd.sqrtd (by norm_num)
  exact hpmonic.isPrimitive.irreducible_of_irreducible_map_of_injective
    (IsFractionRing.injective R K) hpmap

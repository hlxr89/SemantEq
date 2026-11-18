import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra ℚ R] [IsScalarTower ℚ R R] : Irreducible ((Polynomial.X ^ 2 - 2 : Polynomial ℚ).map (algebraMap ℚ R)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have h := dummy_assumed (R := ℝ)
  have hfac :
      ((Polynomial.X ^ 2 - 2 : Polynomial ℚ).map (algebraMap ℚ ℝ)) =
        (X - C (Real.sqrt 2)) * (X + C (Real.sqrt 2)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat]
    symm
    calc
      (X - C (Real.sqrt 2)) * (X + C (Real.sqrt 2)) =
          X ^ 2 - (C (Real.sqrt 2)) ^ 2 := by ring
      _ = X ^ 2 - 2 := by
        rw [← Polynomial.C_pow,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Polynomial.C_ofNat]
  rw [hfac] at h
  rcases h.isUnit_or_isUnit rfl with h₁ | h₂
  · have hn := Polynomial.natDegree_eq_zero_of_isUnit h₁
    rw [Polynomial.natDegree_X_sub_C] at hn
    norm_num at hn
  · have hn := Polynomial.natDegree_eq_zero_of_isUnit h₂
    rw [Polynomial.natDegree_X_add_C] at hn
    norm_num at hn

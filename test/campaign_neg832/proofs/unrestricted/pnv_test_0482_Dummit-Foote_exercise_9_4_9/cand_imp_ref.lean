import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (sqrt_two : R) (h : sqrt_two ^ 2 = 2) : Irreducible (Polynomial.C (sqrt_two) * Polynomial.X ^ 2 - Polynomial.C (sqrt_two)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hirr := dummy_assumed (R := ℝ) (Real.sqrt 2) hsqrt
  have hfac :
      C (Real.sqrt 2) * X ^ 2 - C (Real.sqrt 2) =
        (C (Real.sqrt 2) * (X - C 1)) * (X + C 1) := by
    norm_num
    ring
  have hleft : ¬ IsUnit (C (Real.sqrt 2) * (X - C 1) : Polynomial ℝ) := by
    intro hu
    obtain ⟨r, -, heq⟩ := Polynomial.isUnit_iff.mp hu
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 1) heq
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
    simp [Polynomial.coeff_one] at hcoeff
    exact hsqrt_ne hcoeff.symm
  have hright : ¬ IsUnit (X + C 1 : Polynomial ℝ) := by
    intro hu
    obtain ⟨r, -, heq⟩ := Polynomial.isUnit_iff.mp hu
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 1) heq
    norm_num [Polynomial.coeff_one] at hcoeff
  rcases hirr.isUnit_or_isUnit hfac with hu | hu
  · exact (hleft hu).elim
  · exact (hright hu).elim

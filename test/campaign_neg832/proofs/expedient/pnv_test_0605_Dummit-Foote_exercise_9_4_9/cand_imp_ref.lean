import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] (x : R) (hx : x ≠ 0) (hx' : ∀ y : R, y * y = 2 → y = x ∨ y = -x) : Irreducible (X^2 - C x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have hsqrt : ∀ y : ℤ, y * y = 2 → y = (4 : ℤ) ∨ y = -(4 : ℤ) := by
    intro y hy
    have hlo : -2 < y := by nlinarith [sq_nonneg (y + 2)]
    have hhi : y < 2 := by nlinarith [sq_nonneg (y - 2)]
    interval_cases y <;> norm_num at hy
  have h := dummy_assumed (R := ℤ) 4 (by norm_num) hsqrt
  have hfactor :
      (X ^ 2 - C (4 : ℤ) : Polynomial ℤ) = (X - C 2) * (X + C 2) := by
    ring_nf
    norm_num
  rcases h.isUnit_or_isUnit hfactor with hu | hu
  · exact ((Polynomial.not_isUnit_of_degree_pos (X - C (2 : ℤ)) (by rw [degree_X_sub_C]; decide)) hu).elim
  · exact ((Polynomial.not_isUnit_of_degree_pos (X + C (2 : ℤ)) (by rw [degree_X_add_C]; decide)) hu).elim

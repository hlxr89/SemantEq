import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {R : Type*} [EuclideanDomain R] [IsDomain R] (h : (2 : R) ≠ 0) : Irreducible (X^2 - 2*X + 2 : R[X]) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  have hirr := dummy_assumed (R := GaussianInt) (by norm_num)
  let i : GaussianInt := Zsqrtd.sqrtd
  have hi : i * i = -1 := by
    apply Zsqrtd.ext <;> norm_num [i]
  have hs : (1 + i) + (1 - i) = 2 := by ring
  have hp : (1 + i) * (1 - i) = 2 := by
    calc
      (1 + i) * (1 - i) = 1 - i * i := by ring
      _ = 2 := by rw [hi]; norm_num
  have hfac : (X^2 - 2*X + 2 : GaussianInt[X]) =
      (X - C (1 + i)) * (X - C (1 - i)) := by
    calc
      (X^2 - 2*X + 2 : GaussianInt[X]) =
          X^2 - C ((1 + i) + (1 - i)) * X + C ((1 + i) * (1 - i)) := by
            rw [hs, hp]
            simp only [Polynomial.C_ofNat]
      _ = (X - C (1 + i)) * (X - C (1 - i)) := by
            simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul]
            ring
  have hn₁ : ¬ IsUnit (X - C (1 + i) : GaussianInt[X]) :=
    Polynomial.not_isUnit_of_degree_pos _ (by rw [Polynomial.degree_X_sub_C]; norm_num)
  have hn₂ : ¬ IsUnit (X - C (1 - i) : GaussianInt[X]) :=
    Polynomial.not_isUnit_of_degree_pos _ (by rw [Polynomial.degree_X_sub_C]; norm_num)
  exact False.elim <| (hirr.isUnit_or_isUnit hfac).elim hn₁ hn₂

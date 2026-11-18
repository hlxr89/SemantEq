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
  exfalso
  have hs : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [Real.mul_self_sqrt]
    norm_num
  have hi : Irreducible (X^2 - C (Real.sqrt 2) : Polynomial ℝ) :=
    dummy_assumed (Real.sqrt 2) hs
  let x : ℝ := Real.sqrt (Real.sqrt 2)
  have hx : IsRoot (X^2 - C (Real.sqrt 2) : Polynomial ℝ) x := by
    change eval x (X^2 - C (Real.sqrt 2) : Polynomial ℝ) = 0
    simp [x, Real.sq_sqrt (Real.sqrt_nonneg 2)]
  have hd := degree_eq_one_of_irreducible_of_root hi hx
  rw [degree_X_pow_sub_C (by omega) (Real.sqrt 2)] at hd
  norm_num at hd

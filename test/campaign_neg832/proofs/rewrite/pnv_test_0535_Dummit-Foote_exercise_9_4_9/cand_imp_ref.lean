import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [CommRing α] [IsDomain α] [UniqueFactorizationMonoid α] (sqrt2 : α) (h : sqrt2 * sqrt2 = 2) : Irreducible (Polynomial.C sqrt2 * Polynomial.X ^ 2 - Polynomial.C 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_9 :
  Irreducible (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
  let sqrt2 : ℝ := Real.sqrt 2
  have hsqrt2 : sqrt2 * sqrt2 = 2 := by
    exact Real.mul_self_sqrt zero_le_two
  let r : {x : ℝ // x * x = (2 : ℤ)} := ⟨sqrt2, hsqrt2⟩
  let φ : Zsqrtd 2 →+* ℝ := Zsqrtd.lift r
  have htwo_nonsquare : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
    intro n hn
    have hn_unit : IsUnit n :=
      (Int.prime_two.irreducible.isUnit_or_isUnit hn).elim id id
    rcases Int.isUnit_iff.mp hn_unit with rfl | rfl <;> cases hn
  letI : IsDomain (Zsqrtd 2) :=
    (Zsqrtd.lift_injective r htwo_nonsquare).isDomain φ
  have h_assumed := dummy_assumed sqrt2 hsqrt2
  have hsqrt2_unit : IsUnit (C sqrt2 : Polynomial ℝ) := by
    apply IsUnit.map (Polynomial.C : ℝ →+* Polynomial ℝ)
    apply isUnit_iff_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact two_pos
  have hfactor :
      C sqrt2 * X ^ 2 - C (2 : ℝ) = C sqrt2 * (X ^ 2 - C sqrt2) := by
    rw [mul_sub, ← C_mul, hsqrt2]
  have hmapped :
      (X ^ 2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)).map φ =
        (X ^ 2 - C sqrt2 : Polynomial ℝ) := by
    dsimp only [φ]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    simp only [Zsqrtd.lift_apply_apply, Zsqrtd.re_sqrtd, Int.cast_zero,
      Zsqrtd.im_sqrtd, Int.cast_one, zero_add, one_mul, r]
  apply (Polynomial.monic_X_pow_sub_C Zsqrtd.sqrtd (Nat.succ_ne_zero 1)).irreducible_of_irreducible_map φ
  rw [hmapped]
  exact (hfactor ▸ associated_unit_mul_left
    (X ^ 2 - C sqrt2 : Polynomial ℝ) (C sqrt2) hsqrt2_unit).irreducible h_assumed

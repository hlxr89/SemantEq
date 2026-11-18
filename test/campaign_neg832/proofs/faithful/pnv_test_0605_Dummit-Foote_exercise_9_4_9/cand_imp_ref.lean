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
  have hnonsquare : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
    intro n hn
    have hnlt : n < 2 := by
      by_contra h
      push_neg at h
      nlinarith
    have hnneglt : -2 < n := by
      by_contra h
      push_neg at h
      nlinarith
    interval_cases n <;> norm_num at hn
  letI : NoZeroDivisors (Zsqrtd 2) :=
    { eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} hab => by
        have hab' : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
          rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
        rcases mul_eq_zero.mp hab' with ha | hb
        · exact Or.inl ((Zsqrtd.norm_eq_zero hnonsquare a).mp ha)
        · exact Or.inr ((Zsqrtd.norm_eq_zero hnonsquare b).mp hb) }
  letI : IsDomain (Zsqrtd 2) := NoZeroDivisors.to_isDomain (Zsqrtd 2)
  let K := FractionRing (Zsqrtd 2)
  let s : K := algebraMap (Zsqrtd 2) K Zsqrtd.sqrtd
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    intro h
    have hz : (Zsqrtd.sqrtd : Zsqrtd 2) = 0 :=
      (IsFractionRing.injective (Zsqrtd 2) K) (by simpa using h)
    have := congrArg Zsqrtd.im hz
    simp at this
  have hs_sq : s * s = (2 : K) := by
    dsimp [s]
    change algebraMap (Zsqrtd 2) K Zsqrtd.sqrtd *
      algebraMap (Zsqrtd 2) K Zsqrtd.sqrtd = 2
    rw [← map_mul, Zsqrtd.dmuld]
    exact map_ofNat (algebraMap (Zsqrtd 2) K) 2
  have hs_roots : ∀ y : K, y * y = 2 → y = s ∨ y = -s := by
    intro y hy
    have hfac : (y - s) * (y + s) = 0 := by
      calc
        (y - s) * (y + s) = y * y - s * s := by ring
        _ = 0 := by rw [hy, hs_sq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hK : Irreducible (X^2 - C s : Polynomial K) :=
    dummy_assumed s hs_ne hs_roots
  have hmonic : Monic (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) := by
    exact monic_X_pow_sub_C (R := Zsqrtd 2) (n := 2) Zsqrtd.sqrtd (by omega)
  apply Polynomial.Monic.irreducible_of_irreducible_map
    (algebraMap (Zsqrtd 2) K)
    (X^2 - C Zsqrtd.sqrtd : Polynomial (Zsqrtd 2)) hmonic
  simpa [s] using hK

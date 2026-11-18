import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_10_1_assumed {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {G : Type*} [Group G] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b^p = 1) (hp : Nat.Prime p) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  letI : A.Normal := hA
  have hb_ne_one : b ≠ 1 := by
    intro hb_one
    apply hbA
    rw [hb_one]
    exact Subgroup.one_mem A
  have horder_dvd : orderOf b ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr hb
  have horder : orderOf b = p := by
    rcases (Nat.dvd_prime hp).mp horder_dvd with horder_one | horder_p
    · exact False.elim (hb_ne_one (orderOf_eq_one_iff.mp horder_one))
    · exact horder_p
  have horder_prime : Nat.Prime (orderOf b) := by
    rw [horder]
    exact hp
  rw [Subgroup.zpowers_eq_closure]
  exact exercise_2_10_1_assumed A hbA horder_prime

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
theorem dummy {G : Type*} [Group G] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b ^ p = 1) (hp : Nat.Prime p) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  letI : A.Normal := hA
  rw [Subgroup.zpowers_eq_closure]
  apply exercise_2_10_1_assumed A hbA
  have hord_dvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hb
  have hord_ne_one : orderOf b ≠ 1 := by
    intro hord
    apply hbA
    have hb_one : b = 1 := orderOf_eq_one_iff.mp hord
    simpa [hb_one]
  have hord_eq : orderOf b = p :=
    ((Nat.dvd_prime hp).mp hord_dvd).resolve_left hord_ne_one
  rw [hord_eq]
  exact hp

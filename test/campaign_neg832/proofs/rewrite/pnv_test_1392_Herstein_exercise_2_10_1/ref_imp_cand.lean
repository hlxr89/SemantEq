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
  have hordvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hb
  have hordne : orderOf b ≠ 1 := by
    intro hord
    apply hbA
    rw [orderOf_eq_one_iff.mp hord]
    exact A.one_mem
  have hord : orderOf b = p :=
    (hp.eq_one_or_self_of_dvd (orderOf b) hordvd).resolve_left hordne
  rw [Subgroup.zpowers_eq_closure]
  apply exercise_2_10_1_assumed A hbA
  rw [hord]
  exact hp

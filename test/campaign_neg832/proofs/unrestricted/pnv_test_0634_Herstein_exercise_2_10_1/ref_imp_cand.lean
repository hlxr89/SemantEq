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
theorem dummy {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal] {b : G} (hb : b ^ p = 1) (hp : Nat.Prime p) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  have hb_ne_one : b ≠ 1 := by
    intro h
    apply hbA
    simpa [h]
  have hord_dvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hb
  have hord_ne_one : orderOf b ≠ 1 := by
    intro h
    apply hb_ne_one
    exact orderOf_eq_one_iff.mp h
  have hord_eq : orderOf b = p :=
    (hp.eq_one_or_self_of_dvd (orderOf b) hord_dvd).resolve_left hord_ne_one
  have hord_prime : Nat.Prime (orderOf b) := by
    simpa [hord_eq] using hp
  rw [Subgroup.zpowers_eq_closure]
  exact exercise_2_10_1_assumed A hbA hord_prime

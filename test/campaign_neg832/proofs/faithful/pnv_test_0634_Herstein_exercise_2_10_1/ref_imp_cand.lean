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
    simpa [h] using A.one_mem
  have horder_ne_one : orderOf b ≠ 1 := by
    intro h
    exact hb_ne_one (orderOf_eq_one_iff.mp h)
  have horder_dvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hb
  have horder_eq : orderOf b = p :=
    (hp.eq_one_or_self_of_dvd (orderOf b) horder_dvd).resolve_left horder_ne_one
  have horder_prime : Nat.Prime (orderOf b) := by
    simpa [horder_eq] using hp
  have h := exercise_2_10_1_assumed A hbA horder_prime
  simpa only [Subgroup.zpowers_eq_closure] using h

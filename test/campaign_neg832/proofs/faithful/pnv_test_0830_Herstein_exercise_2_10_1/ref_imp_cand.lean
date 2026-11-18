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
theorem dummy {G : Type*} [Group G] {A : Subgroup G} [A.Normal] {b : G} {p : ℕ} [hp : Fact (Nat.Prime p)] (hb : b ^ p = 1) (hbnA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  have hord_dvd : orderOf b ∣ p := orderOf_dvd_of_pow_eq_one hb
  have hord_ne_one : orderOf b ≠ 1 := by
    intro hord
    have hb_one : b = 1 := orderOf_eq_one_iff.mp hord
    exact hbnA (hb_one.symm ▸ A.one_mem)
  have hord : orderOf b = p :=
    ((Nat.dvd_prime hp.out).mp hord_dvd).resolve_left hord_ne_one
  have href := exercise_2_10_1_assumed A hbnA (hord ▸ hp.out)
  simpa only [Subgroup.zpowers_eq_closure] using href

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
  rw [Subgroup.zpowers_eq_closure]
  apply exercise_2_10_1_assumed A hbnA
  have hne : orderOf b ≠ 1 := fun h ↦ hbnA (by
    rw [orderOf_eq_one_iff.mp h]
    exact A.one_mem)
  simpa [(hp.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hb)).resolve_left hne]
    using hp.out

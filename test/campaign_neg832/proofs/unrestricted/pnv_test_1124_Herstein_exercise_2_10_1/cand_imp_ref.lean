import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {A : Subgroup G} (hA : A.Normal) {b : G} (hb : b^p = 1) (hp : Nat.Prime p) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  rw [← Subgroup.zpowers_eq_closure]
  exact dummy_assumed (A := A) (inferInstance : A.Normal)
    (pow_orderOf_eq_one b) hp hb

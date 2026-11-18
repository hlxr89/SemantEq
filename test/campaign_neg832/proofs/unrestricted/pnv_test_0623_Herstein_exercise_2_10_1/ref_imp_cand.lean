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
theorem dummy {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal] {p : ℕ} [hp : Fact p.Prime] {b : G} (hb : b ^ p = 1) (hbA : b ∉ A) : A ⊓ Subgroup.zpowers b = ⊥ := by
  have hb1 : b ≠ 1 := by
    intro h
    apply hbA
    simpa [h]
  have horder : orderOf b = p := orderOf_eq_prime hb hb1
  rw [Subgroup.zpowers_eq_closure]
  apply exercise_2_10_1_assumed A hbA
  simpa [horder] using hp.out

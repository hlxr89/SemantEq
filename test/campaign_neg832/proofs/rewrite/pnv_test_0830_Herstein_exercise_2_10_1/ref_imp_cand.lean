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
  have hb1 : b ≠ 1 := by
    intro h
    apply hbnA
    rw [h]
    exact A.one_mem
  have horder : orderOf b = p := orderOf_eq_prime hb hb1
  have hprime : Nat.Prime (orderOf b) := by
    rw [horder]
    exact hp.out
  simpa only [Subgroup.zpowers_eq_closure] using
    exercise_2_10_1_assumed A hbnA hprime

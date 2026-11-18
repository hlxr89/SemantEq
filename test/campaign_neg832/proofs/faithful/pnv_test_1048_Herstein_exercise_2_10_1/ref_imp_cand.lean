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
theorem dummy {G : Type*} [Group G] {A : Subgroup G} [hA : A.Normal] {b : G} (hb : b ∉ A) (hp : ∀ n : ℕ, b ^ n = 1 ↔ n % p = 0) (hp_prime : Fact (Nat.Prime p)) : A ⊓ Subgroup.zpowers b = ⊥ := by
  have hb_ne_one : b ≠ 1 := fun h => hb (h.symm ▸ A.one_mem)
  have hbp : b ^ p = 1 := (hp p).2 (Nat.mod_self p)
  have horder : orderOf b = p := orderOf_eq_prime hbp hb_ne_one
  rw [Subgroup.zpowers_eq_closure]
  exact exercise_2_10_1_assumed A hb (horder ▸ hp_prime.out)

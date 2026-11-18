import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] {A : Subgroup G} [hA : A.Normal] {b : G} (hb : b ∉ A) (hp : ∀ n : ℕ, b ^ n = 1 ↔ n % p = 0) (hp_prime : Fact (Nat.Prime p)) : A ⊓ Subgroup.zpowers b = ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_10_1 {G : Type*} [Group G] (A : Subgroup G)
  [A.Normal] {b : G} (hb : b ∉ A) (hp : Nat.Prime (orderOf b)) :
  A ⊓ (Subgroup.closure {b}) = ⊥ := by
  have hpow : ∀ n : ℕ, b ^ n = 1 ↔ n % orderOf b = 0 := by
    intro n
    rw [← Nat.dvd_iff_mod_eq_zero, orderOf_dvd_iff_pow_eq_one]
  rw [← Subgroup.zpowers_eq_closure]
  exact dummy_assumed hb hpow ⟨hp⟩

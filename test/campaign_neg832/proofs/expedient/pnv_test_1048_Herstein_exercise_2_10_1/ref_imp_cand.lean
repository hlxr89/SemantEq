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
  have hpow (n : ℕ) : b ^ n = 1 ↔ p ∣ n :=
    (hp n).trans Nat.dvd_iff_mod_eq_zero.symm
  have horder : orderOf b = p := Nat.dvd_antisymm
    ((orderOf_dvd_iff_pow_eq_one).2 ((hpow p).2 (dvd_refl p)))
    ((hpow (orderOf b)).1 ((orderOf_dvd_iff_pow_eq_one).1 (dvd_refl _)))
  simpa [Subgroup.zpowers_eq_closure, horder] using
    exercise_2_10_1_assumed A hb (horder.symm ▸ hp_prime.out)

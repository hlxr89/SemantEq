import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {A : Subgroup G} [hA : A.Normal] {b : G} (hb : b ∉ A) (hp : ∀ n : ℕ, b ^ n = 1 ↔ n % p = 0) (hp_prime : Fact (Nat.Prime p)) : A ⊓ Subgroup.zpowers b = ⊥ := sorry

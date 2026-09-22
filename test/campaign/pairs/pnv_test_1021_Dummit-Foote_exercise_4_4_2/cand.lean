import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p q : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)] (hpq : p ≠ q) (hG : Fintype.card G = p * q) (hGabelian : ∀ a b : G, a * b = b * a) : IsCyclic G := sorry

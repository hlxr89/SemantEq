import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p q : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)] (h : Fintype.card G = p * q) (hG : ∀ x y : G, x * y = y * x) : IsCyclic G := sorry

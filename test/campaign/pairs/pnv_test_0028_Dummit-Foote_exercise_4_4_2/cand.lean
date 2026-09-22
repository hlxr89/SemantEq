import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) (hG : Fintype.card G = p * q) (hGabelian : ∀ a b : G, a * b = b * a) : IsCyclic G := sorry

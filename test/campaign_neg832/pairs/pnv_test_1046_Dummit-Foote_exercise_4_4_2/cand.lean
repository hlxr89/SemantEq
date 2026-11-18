import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] [DecidableEq G] (p q : ℕ) (hp : Fact p.Prime) (hq : Fact q.Prime) (h_neq : p ≠ q) (hG : Fintype.card G = p * q) : ∃ g : G, ∀ x : G, x = g ^ (Fintype.card G / gcd p q) := sorry

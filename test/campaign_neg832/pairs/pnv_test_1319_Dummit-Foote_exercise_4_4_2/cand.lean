import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hG : Fintype.card G = p * q) : IsCyclic G := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] {p q : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] [DecidableEq G] (h : Fintype.card G = p * q) : IsCyclic G := sorry

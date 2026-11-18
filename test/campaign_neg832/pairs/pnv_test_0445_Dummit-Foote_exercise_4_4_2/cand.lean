import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] (p q : ℕ) (hp : Fact p.Prime) (hq : Fact q.Prime) (h : Fintype.card G = p * q) (hp_neq_q : p ≠ q) : IsCyclic G := sorry

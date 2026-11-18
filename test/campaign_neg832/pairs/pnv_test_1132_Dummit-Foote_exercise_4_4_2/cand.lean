import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [Fintype G] [DecidableEq G] (hp : Fintype.card G = p * q) (hp1 : Fact p.Prime) (hp2 : Fact q.Prime) (h_distinct : p ≠ q) : IsCyclic G := sorry

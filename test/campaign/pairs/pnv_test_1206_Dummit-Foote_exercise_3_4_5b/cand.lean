import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (hG : IsSolvable G) (N : Subgroup G) (hN : Normal N) : IsSolvable (G ⧸ N) := sorry

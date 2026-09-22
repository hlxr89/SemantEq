import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) (hG : IsSolvable G) : IsSolvable (G ⧸ N) := sorry

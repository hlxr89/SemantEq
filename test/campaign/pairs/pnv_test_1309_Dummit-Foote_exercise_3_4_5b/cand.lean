import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H : Subgroup G} (hG : IsSolvable G) (hH : H.Normal) : IsSolvable (G ⧸ H) := sorry

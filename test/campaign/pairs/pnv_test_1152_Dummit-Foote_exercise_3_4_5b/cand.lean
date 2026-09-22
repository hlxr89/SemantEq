import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] [IsSolvable G] {H : Subgroup G} (hH : Normal H) : IsSolvable (G ⧸ H) := sorry

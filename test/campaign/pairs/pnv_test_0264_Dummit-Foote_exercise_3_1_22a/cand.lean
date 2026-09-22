import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (H K : Subgroup G) [hH : Normal H] [hK : Normal K] : Normal (H ⊓ K) := sorry

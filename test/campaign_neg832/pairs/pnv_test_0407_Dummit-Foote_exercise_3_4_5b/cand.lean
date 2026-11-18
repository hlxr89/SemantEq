import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G H : Type*} [Group G] [Group H] [hG : IsSolvable G] (f : G →* H) : IsSolvable H := sorry

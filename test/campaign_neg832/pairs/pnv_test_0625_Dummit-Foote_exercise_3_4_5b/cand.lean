import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (G' : Type*) [Group G'] (f : G →* G') (hf : Function.Surjective f) (h1 : IsSolvable G) : IsSolvable G' := sorry

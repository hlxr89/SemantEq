import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H K : Subgroup G} [Fintype H] [Fintype K] (hH : Nat.Coprime (Fintype.card H) (Fintype.card K)) : H ⊓ K = ⊥ := sorry

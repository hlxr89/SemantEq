import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hH : FiniteIndex H) (hK : FiniteIndex K) (hgcd : Nat.gcd H.index K.index = 1) : H ⊓ K = ⊥ := sorry

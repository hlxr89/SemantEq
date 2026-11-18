import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (H K : Subgroup G) (hH : Finite H) (hK : Finite K) (hcop : IsCoprime (H.index : ℕ) (K.index)) : H ⊓ K = ⊥ := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) (hH : H.Characteristic) (hK : K.Normal) : H.Normal := sorry

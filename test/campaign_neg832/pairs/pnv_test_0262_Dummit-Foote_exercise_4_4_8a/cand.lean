import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) (hHcharK : H.Characteristic) (hKnormalG : K.Normal) : H.Normal := sorry

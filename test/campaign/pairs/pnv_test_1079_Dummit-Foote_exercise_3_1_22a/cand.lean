import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊓ K).Normal := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (G : Type*) [Group G] (H K : Subgroup G) (h : H ≤ K) (hK_normal : (normalizer H : Subgroup G) ≤ K) (hH_normal : normalizer H = H) : (normalizer H : Subgroup G) ≤ normalizer K := sorry

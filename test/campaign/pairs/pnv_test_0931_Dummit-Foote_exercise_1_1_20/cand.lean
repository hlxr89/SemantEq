import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] (x : G) : orderOf (x⁻¹) = orderOf x := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [Group G] (x : G) : orderOf x = orderOf x⁻¹ := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [Group G] (x : G) (hx : IsOfFinOrder x) : x ^ (orderOf x - 1) = x⁻¹ := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R} [Ring R] [IsDomain R] {x : R} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := sorry

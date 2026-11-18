import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (x : ℤ[X]) : Irreducible (x^4 - 4*x^3 + 6) := sorry

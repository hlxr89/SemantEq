import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (x : R) : Irreducible (x^4 - 4*x^3 + 6) := sorry

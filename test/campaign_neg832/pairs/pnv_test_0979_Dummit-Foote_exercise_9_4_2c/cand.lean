import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] : Irreducible (X ^ 4 + (4 : R[X]) * X ^ 3 + 6 * X ^ 2 + (2 : R[X]) * X + 1) := sorry

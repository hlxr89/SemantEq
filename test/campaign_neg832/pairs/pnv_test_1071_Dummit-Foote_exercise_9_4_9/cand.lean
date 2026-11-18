import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] {a : R} (ha2 : a ^ 2 = 2) : Irreducible (X^2 - C a) := sorry

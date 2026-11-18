import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (p : R[X]) (h : p = X^4 + 4*X^3 + 6*X^2 + 2*X + 1) : Irreducible p := sorry

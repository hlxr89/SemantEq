import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] {f : R[X]} (hf : f = X^3 + 3*X + 2) : Irreducible f := sorry

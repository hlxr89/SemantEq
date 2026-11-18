import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] : Irreducible (X^2 + X + 1 : Polynomial R) := sorry

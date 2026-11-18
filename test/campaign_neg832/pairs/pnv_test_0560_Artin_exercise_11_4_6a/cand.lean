import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]: Irreducible (X^2 + X + 1 : R[X]) := sorry

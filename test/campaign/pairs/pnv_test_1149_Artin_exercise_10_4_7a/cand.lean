import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] {I J : Ideal R} (hIJ : I + J = ⊤) : I * J = I ⊓ J := sorry

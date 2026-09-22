import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type u} [CommRing R] (I J : Ideal R) (h : I + J = ⊤) : I * J = I ⊓ J := sorry

import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] {x : R} (hx : IsNilpotent x) : IsUnit (1 + x) := sorry

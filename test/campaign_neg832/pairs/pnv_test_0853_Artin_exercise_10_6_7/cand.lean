import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy (I : Ideal (GaussianInt)) (hI : I ≠ 0) : ∃ z : GaussianInt, z ≠ 0 ∧ z ∈ I := sorry

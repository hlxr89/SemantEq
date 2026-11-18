import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy (I : Ideal (GaussianInt)) (hI : I ≠ 0) : ∃ x : GaussianInt, x ≠ 0 ∧ x ∈ I := sorry

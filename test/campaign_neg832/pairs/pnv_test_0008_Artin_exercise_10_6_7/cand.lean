import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {I : Ideal (GaussianInt)} (hI : I ≠ ⊥) : ∃ n ≠ (0 : ℤ), (n : GaussianInt) ∈ I := sorry

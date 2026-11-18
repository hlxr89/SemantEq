import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : Irreducible (Polynomial.X^3 - 9 : Polynomial ℤ) := sorry

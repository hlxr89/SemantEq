import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : Irreducible (X^3 - 9 : Polynomial (Fin 31 → ℤ)) := sorry

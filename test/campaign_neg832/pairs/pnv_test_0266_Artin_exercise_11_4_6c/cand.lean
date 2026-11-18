import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type _} [Field F] [CharZero F] : Irreducible (X^3 - 9 : F[X]) := sorry

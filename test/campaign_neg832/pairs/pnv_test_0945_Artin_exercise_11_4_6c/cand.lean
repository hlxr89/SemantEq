import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F 31] (p : Polynomial F) (h : p = X^3 - 9) : Irreducible p := sorry

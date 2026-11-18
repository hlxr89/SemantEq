import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F 31] {x : F} (h : x^3 - 9 ≠ 0) : Irreducible (x^3 - 9) := sorry

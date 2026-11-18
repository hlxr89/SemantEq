import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {R : Type*} [Field R] [CharP R 2] (p : Polynomial R) (h : p ≠ 0) (h1 : ¬∃ q r : Polynomial R, r ≠ 0 ∧ degree r < degree p ∧ p = q * r): p = X ^ 2 + X + 1 := sorry

import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy (p : ℕ) [hp : Fact p.Prime] : Irreducible (X^3 - C 9 : Polynomial (ZMod p)) := sorry

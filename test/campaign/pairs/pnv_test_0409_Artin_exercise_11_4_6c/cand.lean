import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp31 : p = 31) : Irreducible (X^3 - 9 : Polynomial (ZMod p)) := sorry

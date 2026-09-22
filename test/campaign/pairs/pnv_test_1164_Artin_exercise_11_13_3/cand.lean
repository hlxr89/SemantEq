import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : ∃ᶠ p in at_top, Nat.Prime p ∧ p % 4 = 3 := sorry

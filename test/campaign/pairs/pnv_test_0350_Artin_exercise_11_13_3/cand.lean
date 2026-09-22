import Mathlib

open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators

theorem dummy : Infinite {p : ℕ | Nat.Prime p ∧ p % 4 = 3} := sorry

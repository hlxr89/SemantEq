import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (a b : ℤ) (h : a^4 + 4*a^3 + 6*a^2 + 2*a + 1 = b) : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 1 := sorry

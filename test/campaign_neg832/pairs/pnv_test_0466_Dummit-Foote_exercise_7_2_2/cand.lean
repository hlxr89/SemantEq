import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [Ring R] (p : R[X]) (b : R) : p * C b = 0 ↔ b = 0 ∨ p = 0 := sorry

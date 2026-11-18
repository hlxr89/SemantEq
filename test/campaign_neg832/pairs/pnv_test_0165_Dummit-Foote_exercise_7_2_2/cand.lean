import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] {p : R[X]} : p ∈ nonZeroDivisors R[X] ↔ p ≠ 0 := sorry

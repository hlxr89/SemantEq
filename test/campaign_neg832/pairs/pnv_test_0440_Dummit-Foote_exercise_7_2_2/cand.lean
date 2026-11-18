import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] {f : R[X]} : f ∈ nonZeroDivisors R[X] ↔ f ≠ 0 := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommSemiring R] {p : R[X]} : p ∈ Ideal.span {X} ↔ ∃ b : R, b ≠ 0 ∧ b • p = 0 := sorry

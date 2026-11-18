import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (p : R[X]) : p ∈ Ideal.span ({0} : Set R[X]) ↔ ∃ (b : R), b ≠ 0 ∧ b • p = 0 := sorry

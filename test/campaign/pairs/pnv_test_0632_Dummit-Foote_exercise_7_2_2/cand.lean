import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] {p : R[X]} : (∃ q : R[X], q ≠ 0 ∧ p * q = 0) ↔ (∃ b : R, b ≠ 0 ∧ b • p = 0) := sorry

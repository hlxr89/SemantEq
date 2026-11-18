import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (f : R[X]) (h : f = X^4 - 4 * X^3 + 6) : ¬ ∃ (g : R[X]) (h : R[X]), f = g * (X - 1) * (X - 2) * (X - 3) := sorry

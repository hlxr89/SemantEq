import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] [IsDomain R] {p : R[X]} (h : p = X^4 - 4 * X^3 + 6) : Irreducible p := sorry

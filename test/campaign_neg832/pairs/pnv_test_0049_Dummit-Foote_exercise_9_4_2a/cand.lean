import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] [IsDomain R] (f : R[X]) (h : f = X ^ 4 - 4 * X ^ 3 + 6) : ¬ ∃ (p q : R[X]), p * q = f ∧ 0 < degree p ∧ 0 < degree q := sorry

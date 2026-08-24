import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (h : ∀ (a : R), a ^ 2 = a) : ∀ a b : R, a * b = b * a := sorry

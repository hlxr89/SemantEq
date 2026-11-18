import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (R : Type*) [CommRing R] (a : R) (ha : IsNilpotent a) (b : R) : IsUnit (1 - a * b) := sorry

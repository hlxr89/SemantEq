import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [Nontrivial R] {a b : R} (ha : IsNilpotent a) (hb : IsUnit b) : IsUnit (1 - a * b) := sorry

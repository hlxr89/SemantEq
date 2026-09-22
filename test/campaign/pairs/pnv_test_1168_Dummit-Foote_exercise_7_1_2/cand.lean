import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [CommRing R] {u : R} (hu : IsUnit u) : IsUnit (-u) := sorry

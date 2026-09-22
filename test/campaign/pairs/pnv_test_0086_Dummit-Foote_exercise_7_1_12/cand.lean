import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [Field R] {S : Subring R} (hS : 1 ∈ S) : IsDomain S := sorry

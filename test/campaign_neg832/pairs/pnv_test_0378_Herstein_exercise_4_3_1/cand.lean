import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy [CommRing R] {I : Ideal R} {x : R} (hx : x ∈ I) : (I : Set R) ⊆ span {x} := sorry

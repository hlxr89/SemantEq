import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) : (φ '' (center R)) ⊆ center S := sorry

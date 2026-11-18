import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f) : f '' (center R) ⊆ center S := sorry

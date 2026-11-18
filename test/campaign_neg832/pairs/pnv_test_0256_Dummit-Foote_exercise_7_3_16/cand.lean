import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] (f : R →+* S) (hf : Function.Surjective f) : f '' ((center R : Set R) : Set R) ⊆ (center S : Set S) := sorry

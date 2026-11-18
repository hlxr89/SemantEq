import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] : ∃ S : Set (Ideal R), Set.Infinite S ∧ ∀ I ∈ S, Ideal.IsPrime I ∧ I.IsMaximal := sorry

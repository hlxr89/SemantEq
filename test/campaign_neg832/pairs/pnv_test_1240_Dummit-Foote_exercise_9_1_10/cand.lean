import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (R : Type*) [CommRing R] : ∃ (S : Set (Ideal (Polynomial R))), Infinite S ∧ ∀ I ∈ S, Ideal.IsPrime I ∧ ∀ J ∈ S, J ≤ I → J = I := sorry

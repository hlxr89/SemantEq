import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] : ∃ S : Set (Ideal R), Set.Infinite S ∧ ∀ s t : S, s ≠ t → s.val ≠ t.val := sorry

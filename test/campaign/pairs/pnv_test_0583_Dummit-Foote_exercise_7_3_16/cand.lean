import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) (hφ : Function.Surjective φ) : φ '' (Set.center R) ⊆ Set.center S := sorry

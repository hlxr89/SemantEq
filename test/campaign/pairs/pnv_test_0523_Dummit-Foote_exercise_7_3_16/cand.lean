import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [Ring R] [Ring S] (ϕ : R →+* S) (hϕ : Function.Surjective ϕ) : ϕ '' (Set.center R) ⊆ Set.center S := sorry

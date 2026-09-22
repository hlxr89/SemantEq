import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [Ring R] [Ring S] (ϕ : R →+* S) (hsurj : Function.Surjective ϕ) : ϕ '' (center R) ⊆ center S := sorry

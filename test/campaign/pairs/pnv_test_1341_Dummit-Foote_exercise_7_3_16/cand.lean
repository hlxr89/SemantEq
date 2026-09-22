import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) (φ_surj : Function.Surjective φ) : φ '' center R ⊆ center S := sorry

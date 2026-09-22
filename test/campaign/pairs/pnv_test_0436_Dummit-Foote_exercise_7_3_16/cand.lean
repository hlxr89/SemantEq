import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R S : Type*} [Ring R] [Ring S] (phi : R →+* S) (hphi : Function.Surjective phi) : phi '' (center R) ⊆ center S := sorry

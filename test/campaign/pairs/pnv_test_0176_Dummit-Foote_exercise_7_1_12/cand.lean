import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {K : Type*} [Field K] (S : Subring K) (hS : (1 : K) ∈ S) : IsDomain S := sorry

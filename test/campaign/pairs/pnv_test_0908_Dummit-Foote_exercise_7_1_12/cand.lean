import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {K : Type*} [Field K] (R : Subring K) (hR : (1 : K) ∈ R) : IsDomain R := sorry

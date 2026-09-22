import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [Field R] {S : Subring R} (h : (1 : R) ∈ S) : IsDomain S := sorry

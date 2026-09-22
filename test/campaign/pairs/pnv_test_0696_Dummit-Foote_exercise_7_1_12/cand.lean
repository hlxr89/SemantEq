import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (F : Type*) [Field F] (R : Subring F) (h : (1 : F) ∈ R) : IsDomain R := sorry

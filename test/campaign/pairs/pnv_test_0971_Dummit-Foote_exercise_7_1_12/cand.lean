import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {α : Type*} [Field α] (R : Subring α) (h : (1 : α) ∈ R) : IsDomain R := sorry

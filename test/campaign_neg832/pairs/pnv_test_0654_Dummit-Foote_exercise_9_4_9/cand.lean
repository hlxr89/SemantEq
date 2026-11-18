import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [IsDomain ℤ] [CharZero ℤ] (h : IsIntegrallyClosed ℤ) : Irreducible (X^2 - sqrt₂ : ℤ[X]) := sorry

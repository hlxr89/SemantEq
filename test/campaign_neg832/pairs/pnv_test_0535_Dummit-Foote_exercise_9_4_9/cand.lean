import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {α : Type*} [CommRing α] [IsDomain α] [UniqueFactorizationMonoid α] (sqrt2 : α) (h : sqrt2 * sqrt2 = 2) : Irreducible (Polynomial.C sqrt2 * Polynomial.X ^ 2 - Polynomial.C 2) := sorry

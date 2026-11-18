import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (sqrt_two : R) (h : sqrt_two ^ 2 = 2) : Irreducible (Polynomial.C (sqrt_two) * Polynomial.X ^ 2 - Polynomial.C (sqrt_two)) := sorry

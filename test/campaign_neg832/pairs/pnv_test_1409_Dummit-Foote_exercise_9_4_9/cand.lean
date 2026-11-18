import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (sqrt2 : R) (h : sqrt2 * sqrt2 = 2) : Irreducible (Polynomial.C (sqrt2) * Polynomial.X - Polynomial.C (sqrt2 * sqrt2)) := sorry

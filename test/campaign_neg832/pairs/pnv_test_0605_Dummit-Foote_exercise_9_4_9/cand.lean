import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] (x : R) (hx : x ≠ 0) (hx' : ∀ y : R, y * y = 2 → y = x ∨ y = -x) : Irreducible (X^2 - C x) := sorry

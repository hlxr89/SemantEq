import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra ℚ R] [IsScalarTower ℚ R R] : Irreducible ((Polynomial.X ^ 2 - 2 : Polynomial ℚ).map (algebraMap ℚ R)) := sorry

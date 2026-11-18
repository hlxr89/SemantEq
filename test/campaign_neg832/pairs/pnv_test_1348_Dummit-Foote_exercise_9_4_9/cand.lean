import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] [IsDomain R] [Algebra ℤ R] (hR : ∀ a b : R, Irreducible (a * b) → Irreducible a ∨ Irreducible b) (hsqrt2 : IsIntegral ℤ (sqrt2 : R)) : Irreducible (Polynomial.map (algebraMap ℤ R) (Polynomial.X^2 - C (sqrt2))) := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy : Irreducible (Polynomial.C (6 : ℤ) + Polynomial.C (-4 : ℤ) * Polynomial.X ^ 3 + Polynomial.X ^ 4) := sorry

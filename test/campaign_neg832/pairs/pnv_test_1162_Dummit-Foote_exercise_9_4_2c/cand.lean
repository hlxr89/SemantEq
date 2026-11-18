import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy : Irreducible (Polynomial.C (1 : ℤ) + Polynomial.X + 6 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 3 + Polynomial.X ^ 4) := sorry

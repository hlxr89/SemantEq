import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : Polynomial ℤ) (h : p = Polynomial.C 1 * Polynomial.X ^ 4 + Polynomial.C 4 * Polynomial.X ^ 3 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 1) : Irreducible p := sorry

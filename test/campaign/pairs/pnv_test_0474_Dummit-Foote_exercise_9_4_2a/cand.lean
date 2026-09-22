import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy : Irreducible (Polynomial.X ^ 4 - 4 * Polynomial.X ^ 3 + 6 : Polynomial ℤ) := sorry

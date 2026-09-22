import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (f : Polynomial ℤ) (hf : f = X ^ 4 - 4 * X ^ 3 + 6) : Irreducible f := sorry

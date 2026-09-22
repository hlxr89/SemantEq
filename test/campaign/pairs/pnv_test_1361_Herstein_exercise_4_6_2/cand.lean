import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (f : ℚ[X]) (hf : f = X^3 + 3*X + 2) : Irreducible f := sorry

import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (f : Polynomial ℚ) (hf : f.degree = 3) (hf0 : f.coeff 0 = 2) (hf1 : f.coeff 1 = 3) (hf2 : f.coeff 2 = 1) : Irreducible f := sorry

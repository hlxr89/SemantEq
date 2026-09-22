import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {P : Polynomial ℚ} (hP : P = X^3 + 3*X + 2) : Irreducible P := sorry

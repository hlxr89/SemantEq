import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (F : Type*) [Field F] (hF_char : CharP F 7) : Irreducible (X^3 - 2 : F[X]) ∧ Irreducible (X^3 + 2 : F[X]) := sorry

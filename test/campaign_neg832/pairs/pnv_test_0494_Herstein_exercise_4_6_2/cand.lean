import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [Field R] (f : R[X]) (hf : f.degree = 3) (r : R) (hr : f.IsRoot r) : Irreducible f := sorry

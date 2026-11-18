import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (a : R) (h : a ^ 2 = 0) : ∀ x : R, a * x + x * a = a * (a * x + x * a) := sorry

import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (R : Type u) [CommRing R] (a : R) (h : a * a = 0) (x : R) : (a * x + x * a) = 0 := sorry

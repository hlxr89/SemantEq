import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (a x : R) (h : a * a = 0) : Commute (a * x + x * a) a := sorry

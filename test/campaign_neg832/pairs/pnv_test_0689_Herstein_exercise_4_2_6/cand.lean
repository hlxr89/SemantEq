import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [CommRing R] (a : R) (h : a * a = 0) (x : R) : Commute (a * x + x * a) a := sorry

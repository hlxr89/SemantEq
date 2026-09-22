import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] {a x : R} (h : a^2 = 0) : Commute (a*x + x*a) a := sorry

import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] (a : R) (h : a^2 = 0) (x : R) : Commute a (x + x*a) := sorry

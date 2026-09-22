import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {R : Type*} [Ring R] (a x : R) (h : a^2 = 0) : (a * x + x * a) * a = a * (a * x + x * a) := sorry

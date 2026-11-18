import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy [Ring R] {a : R} (ha : a^2 = 0) : ∀ x : R, a * x + x * a = a * (a * x + x * a) := sorry

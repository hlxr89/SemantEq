import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy (a : ℂ) (h : a ^ 3 = 1) : a = ((-1 + √3*i) / 2) ∨ a = ((-1 - √3*i) / 2) := sorry

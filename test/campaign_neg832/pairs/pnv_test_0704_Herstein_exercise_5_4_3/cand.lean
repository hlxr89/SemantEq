import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy : ¬ (∃ (a : ℝ), (a^5 + (sqrt 2) * a^3 + (sqrt 5) * a^2 + (sqrt 7) * a + (sqrt 11) : ℝ) = 0) := sorry

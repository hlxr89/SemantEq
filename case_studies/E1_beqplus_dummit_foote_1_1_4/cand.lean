import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℕ) (a b c : ℕ) : (a * b) % n * (c % n) % n = a * b * c % n := sorry

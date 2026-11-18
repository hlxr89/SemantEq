import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℕ) (a b c : ℤ) : (a * b)%n * c %n = a * (b * c) %n := sorry

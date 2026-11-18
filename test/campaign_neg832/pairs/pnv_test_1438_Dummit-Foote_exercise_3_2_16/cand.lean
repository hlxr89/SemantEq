import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p a : ℕ) (hp : (p : ℕ) > 1) (ha : a < p) : a^p = a % p := sorry

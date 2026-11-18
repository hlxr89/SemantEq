import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Nat.Prime p) (a : ℕ) : (a ^ p) % p = a % p := sorry

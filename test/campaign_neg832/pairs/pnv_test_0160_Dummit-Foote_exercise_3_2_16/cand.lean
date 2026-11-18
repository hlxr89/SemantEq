import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Nat.Prime p) (a : ℕ) : a ^ p ≡ a [MOD p] := sorry

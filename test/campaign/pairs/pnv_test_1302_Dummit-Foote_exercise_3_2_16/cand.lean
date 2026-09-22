import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : ℕ) (hp : Nat.Prime p) (a : ℤ) : a^p ≡ a [ZMOD p] := sorry

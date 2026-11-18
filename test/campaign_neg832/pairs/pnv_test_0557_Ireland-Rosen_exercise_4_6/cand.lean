import Mathlib

open Real
open scoped BigOperators

theorem dummy (p : ℕ) (hp : Nat.Prime p) (h : p = 2 ^ p + 1) : IsPrimitiveRoot 3 p := sorry

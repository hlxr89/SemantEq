import Mathlib

open Real
open scoped BigOperators

theorem dummy (n : ℕ) (h : Nat.Prime (2^(n) + 1)) : IsPrimitiveRoot 3 (2^(n) + 1) := sorry

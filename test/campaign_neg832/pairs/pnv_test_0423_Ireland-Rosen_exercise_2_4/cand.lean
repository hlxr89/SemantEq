import Mathlib

open Real
open scoped BigOperators

theorem dummy (n m : ℕ) (a : ℤ) (ha : a ≠ 0) (hn : n > m) : gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = if a % 2 = 0 then 1 else 2 := sorry

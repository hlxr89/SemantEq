import Mathlib

open Real
open scoped BigOperators

theorem dummy {a : ℤ} (ha : a ≠ 0) (n m : ℕ) (hnm : n > m) : (gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 1 ∨ gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = 2) := sorry

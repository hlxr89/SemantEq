import Mathlib

open Real
open scoped BigOperators

theorem dummy (a : ℤ) (m n : ℕ) (h : 2 ≤ m) (hmn : m < n) (ha2 : a % 2 = 1) : 2 ∣ (a ^ (2 ^ n) + 1) / (a ^ (2 ^ m) + 1) ∨ 2 ∣ (a ^ (2 ^ n) + 1) / (a ^ (2 ^ m) + 1) := sorry

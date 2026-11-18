import Mathlib

open Real
open scoped BigOperators

theorem dummy {a n m : ℕ} (ha : a ≠ 0) (h : m < n) : gcd (a^(2^n) + 1) (a^(2^m) + 1) = if Even a then 2 else 1 := sorry

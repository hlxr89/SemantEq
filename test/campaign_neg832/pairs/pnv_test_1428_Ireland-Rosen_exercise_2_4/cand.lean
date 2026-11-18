import Mathlib

open Real
open scoped BigOperators

theorem dummy (n m : ℕ) (a : ℤ) : a ≠ 0 → (a^2^n + 1, a^2^m + 1) = (if a % 2 = 0 then 2 else 1) := sorry

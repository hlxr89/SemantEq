import Mathlib

open Real
open scoped BigOperators

theorem dummy {m n : ℕ} {a : ℤ} [NeZero a] (h : m > n) : (a ^ 2 ^ m + 1) ∣ (a ^ 2 ^ n + 1) ∨ (a ^ 2 ^ m + 1) = 2 * (a ^ 2 ^ n + 1) := sorry

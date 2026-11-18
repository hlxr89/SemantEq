import Mathlib

open Real
open scoped BigOperators

theorem dummy (p : ℕ) (hp : p % 4 = 1) : (∃ (x : ℕ), x ^ 4 = 2 * p) ↔ ∃ (a b : ℕ), p = a ^ 2 + 64 * b ^ 2 := sorry

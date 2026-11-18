import Mathlib

open Real
open scoped BigOperators

theorem dummy (p : ℕ) (hp : p % 4 = 1) : ∃ x : ℕ, x ^ 4 % p = 2 ↔ ∃ A B : ℕ, p = A ^ 2 + 64 * B ^ 2 := sorry

import Mathlib

open Real
open scoped BigOperators

theorem dummy (hp : ∃ x : ℤ, x ^ 2 ≡ 1 [ZMOD (p : ℕ)]) : ∃ x : ℤ, x ^ 2 ≡ 2 [ZMOD p] ↔ ∃ A B : ℤ, p = A ^ 2 + 64 * B ^ 2 := sorry

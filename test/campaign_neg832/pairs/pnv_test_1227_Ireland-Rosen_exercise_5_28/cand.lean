import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : p ≡ 1 [MOD 4]) : (∃ x : ℤ, x^4 ≡ 2 [ZMOD p]) ↔ (∃ A B : ℤ, p = A^2 + 64 * B^2) := sorry

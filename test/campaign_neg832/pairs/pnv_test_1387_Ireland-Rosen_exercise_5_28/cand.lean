import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : p ≡ 1 [MOD 4]) : ∃! (x : ℕ), x^4 ≡ 2 [MOD p] ↔ ∃ (A B : ℕ), p = A^2 + 64*B^2 := sorry

import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : p ≡ 1 [MOD 4]) : ∃ (A B : ℕ), p = A ^ 2 + 64 * B ^ 2 ↔ ∃ x, x ^ 4 ≡ 2 [MOD p] := sorry

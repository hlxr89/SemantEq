import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Nat.Prime p) (hp1 : p % 4 = 1) : ∃ (A B : ℤ), p = A^2 + 64 * B^2 := sorry

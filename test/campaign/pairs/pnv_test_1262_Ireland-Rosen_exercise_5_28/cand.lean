import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} [hp : Fact p.Prime] (hp1 : p % 4 = 1) : (∃ x : ℕ, x^4 % p = 2) ↔ ∃ A B : ℤ, p = A^2 + 64 * B^2 := sorry

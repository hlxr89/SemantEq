import Mathlib

open Real
open scoped BigOperators

theorem dummy (p : ℕ) [hp : Fact (p.Prime)] : (∃ x : ℕ, x^4 ≡ 2 [MOD p]) ↔ (∃ A B : ℤ, p = A^2 + 64 * B^2) := sorry

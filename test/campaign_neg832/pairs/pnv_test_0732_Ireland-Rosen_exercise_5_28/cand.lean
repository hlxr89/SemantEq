import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp_prime : Nat.Prime p) (hp_eq : p % 4 = 1) : (∃ n : ℕ, p = n^2 + 64*n^2) ↔ ∃ x : ℤ, 2 * x = 1 ∧ x ^ 4 = p := sorry

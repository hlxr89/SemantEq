import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (hp : ∃ n : ℕ, p = 2^n + 1 ∧ Nat.Prime p) : IsPrimitiveRoot 3 p := sorry

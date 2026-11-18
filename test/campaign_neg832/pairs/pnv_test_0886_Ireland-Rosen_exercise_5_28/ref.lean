import Mathlib

open Real
open scoped BigOperators

theorem exercise_5_28 {p : ℕ} (hp : p.Prime) (hp1 : p ≡ 1 [MOD 4]):
  (∃ x, x^4 ≡ 2 [MOD p]) ↔ ∃ A B, p = A^2 + 64*B^2 := sorry

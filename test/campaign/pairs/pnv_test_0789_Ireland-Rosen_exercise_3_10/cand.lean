import Mathlib

open Real
open scoped BigOperators

theorem dummy (n : ℕ) (hnp : ¬Nat.Prime n) : n.pred.factorial % n = 0 ∨ n = 4 := sorry

import Mathlib

open Real
open scoped BigOperators

theorem dummy {n : ℕ} (h0 : 2 ≤ n) (h1 : n ≠ 2) (hn : n ≠ 3) (hnp : ¬ n.Prime) : Nat.factorial n.pred % n = 0 ∨ Nat.factorial n.pred % n = 1 := sorry

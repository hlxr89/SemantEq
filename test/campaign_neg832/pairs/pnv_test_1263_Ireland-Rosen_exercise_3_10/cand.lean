import Mathlib

open Real
open scoped BigOperators

theorem dummy {n : ℕ} (hn : ¬ Prime n) : n.factorial % n = 0 ∨ n = 4 := sorry

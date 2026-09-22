import Mathlib

open Real
open scoped BigOperators

theorem dummy {n : ℕ} (hn : ¬ Nat.Prime n) (hne4 : n ≠ 4) : (Nat.factorial (n - 1)) % n = 0 := sorry

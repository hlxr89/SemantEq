import Mathlib

open Real
open scoped BigOperators

theorem dummy [Fact (Nat.Prime 2)] (n : ℕ) (h : ¬ Nat.Prime n) : n - 1 ≡ 0 [MOD n] := sorry

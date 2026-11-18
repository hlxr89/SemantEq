import Mathlib

open Real
open scoped BigOperators

theorem dummy (n : ℕ) (hn : ¬n.Prime) : n - 1 ≡ 0 [MOD n] := sorry

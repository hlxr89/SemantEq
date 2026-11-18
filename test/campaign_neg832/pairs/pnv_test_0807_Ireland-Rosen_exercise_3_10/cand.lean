import Mathlib

open Real
open scoped BigOperators

theorem dummy {n : ℕ} (h : ¬ n.Prime) : n.factorial ≡ 0 [MOD n] := sorry

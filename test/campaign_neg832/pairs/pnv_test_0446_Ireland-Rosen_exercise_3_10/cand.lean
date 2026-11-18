import Mathlib

open Real
open scoped BigOperators

theorem dummy {n : ℕ} (h : n ≠ 2 ∧ n ≠ 3) : n - 1 ≡ 0 [MOD n] ∨ n = 4:= sorry

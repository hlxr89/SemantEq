import Mathlib

open scoped BigOperators

theorem dummy {a : ℕ} (ha : 0 < a) : ∃! (n : ℕ), a ^ (n + 1) - (a + 1) ^ n = 2001 := sorry

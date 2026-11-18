import Mathlib

open scoped BigOperators

theorem dummy {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (ha_le : a ≤ n + 1) : a ^ (n + 1) - (a + 1) ^ n = 2001 ↔ a = 2001 ∧ n = 2 := sorry

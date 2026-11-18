import Mathlib

open scoped BigOperators

theorem dummy {a : ℕ} (ha : a > 0) (h : a ^ 2 = 2001): ∃ (a' : ℕ) (n : ℕ), a ^ (n + 1) = Nat.succ a' ^ n ∧ a' > 0 := sorry

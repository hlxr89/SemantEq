import Mathlib

open scoped BigOperators

theorem dummy {n : ℕ} : ∃ (a : ℕ) (H : 1 ≤ a), a ^ (n + 1) - (a + 1) ^ n = 2001 ∧ ∀ (a' : ℕ) (H' : 1 ≤ a'), a ^ (n + 1) - (a + 1) ^ n ≠ 2001 → a' ≠ a := sorry

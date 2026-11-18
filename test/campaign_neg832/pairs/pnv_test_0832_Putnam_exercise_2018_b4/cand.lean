import Mathlib

open scoped BigOperators

theorem dummy {a : ℝ} {n : ℕ} (h : a ^ 2 = 2 * a - 1) (H : (2 ^ n + 1) * a ^ (n + 1) = 2 * a) : ∃ m : ℕ, ∀ k ≥ m, (2 ^ k + 1) * a ^ (k + 1) = 2 * a := sorry

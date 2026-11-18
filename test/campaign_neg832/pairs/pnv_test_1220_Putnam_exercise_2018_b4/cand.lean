import Mathlib

open scoped BigOperators

theorem dummy {a : ℝ} {x : ℕ → ℝ} (hx : x 0 = 1) (hx' : x 1 = x 2) (hx'' : x 2 = a) (hnz : ∃ n : ℕ, x n = 0) : ∃ p : ℕ, ∀ i : ℕ, x (i + p) = x i := sorry

import Mathlib

open scoped BigOperators

theorem dummy (a b c : ℤ) (h : ∃ n : ℕ, √(n^3+a*n^2+b*n+c) ≠ n) : ∃ n : ℕ, 0 < n ∧ √(n^3+a*n^2+b*n+c) ≠ n := sorry

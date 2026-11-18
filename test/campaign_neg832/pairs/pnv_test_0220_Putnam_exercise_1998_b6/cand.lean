import Mathlib

open scoped BigOperators

theorem dummy {a b c : ℤ} : ∃ (n : ℕ) (H : 0 < n), ¬(n : ℝ) ^ 3 + a * n ^ 2 + b * n + c = 0 := sorry

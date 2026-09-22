import Mathlib

open scoped BigOperators

theorem dummy (a b c : ℤ) : ∃ (n : ℤ) (H : n > 0), ¬(∃ (m : ℤ), n ^ 3 + a * n ^ 2 + b * n + c = m ^ 2) := sorry

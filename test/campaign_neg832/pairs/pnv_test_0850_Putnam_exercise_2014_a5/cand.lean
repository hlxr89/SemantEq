import Mathlib

open scoped BigOperators

theorem dummy (s : Finset ℝ) : s.sum id = 0 ↔ (∀ x ∈ s, x = 0) := sorry

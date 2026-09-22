import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (H : AddSubgroup ℚ) (hH : ∀ x ∈ H, x ≠ 0 → (1 / x) ∈ H) : H = ⊥ ∨ H = ⊤ := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {H : AddSubgroup ℚ} (hx : ∀ x ∈ H, ∀ x0 : x ≠ 0, 1 / x ∈ H) : H = ⊥ ∨ H = ⊤ := sorry

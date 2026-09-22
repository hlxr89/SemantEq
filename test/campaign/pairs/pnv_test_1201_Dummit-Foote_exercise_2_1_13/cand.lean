import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {H : AddSubgroup ℚ} (h : ∀ x : ℚ, x ≠ 0 → x ∈ H → 1 / x ∈ H) : H = ⊥ ∨ H = ⊤ := sorry

import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy : ∀ (n : ℕ), Module.rank ℚ (Fin n → ℚ) = 1 := sorry

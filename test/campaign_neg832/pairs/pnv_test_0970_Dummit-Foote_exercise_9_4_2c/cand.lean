import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {p : Polynomial ℝ} : p = X^4 + 4 * X^3 + 6 * X^2 + 2 * X + 1 → ¬(p = (a * X + b) * (c * X + d) ∧ a * c ≠ 0) := sorry

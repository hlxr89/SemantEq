import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {n : ℕ} {a b : Fin n → ℝ} : (∑ j, a j * b j) ^ 2 ≤ (∑ j, (j + 1) * (a j) ^ 2) * (∑ j, (b j) ^ 2 / (j + 1)) := sorry

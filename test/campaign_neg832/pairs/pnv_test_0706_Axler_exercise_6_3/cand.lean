import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {n : ℕ} {a b : Fin n → ℝ} : (∑ j : Fin n, a j * b j)^2 ≤ (∑ j : Fin n, (j : ℝ) * a j^2) * ∑ j : Fin n, b j^2 / j := sorry

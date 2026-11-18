import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {n : ℕ} (a b : Fin n → ℝ) : (∑ i, a i * b i)^2 ≤ ∑ i, i * a i^2 * (1/(i : ℝ)) * ∑ j, j * b j^2 / (j : ℝ) := sorry

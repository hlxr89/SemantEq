import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem exercise_6_3 {n : ℕ} (a b : Fin n → ℝ) :
  (∑ i, a i * b i) ^ 2 ≤ (∑ i : Fin n, (i + 1) * a i ^ 2) * (∑ i, b i ^ 2 / (i + 1)) := sorry

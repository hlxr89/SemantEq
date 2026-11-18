import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {n : ℕ} {a : Fin n → ℝ} {b : Fin n → ℝ} : (∑ i, a i * b i) ^ 2 ≤ (∑ i, i * a i ^ 2) * (∑ i, b i ^ 2 / i) := sorry

import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy : ∃ (U : Set (EuclideanSpace ℝ (Fin 2))), U.Nonempty ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (c : ℝ), x ∈ U → c • x ∈ U ∧ c • x ≠ x := sorry

import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {U : Set (EuclideanSpace ℝ (Fin 2))} : ∃ (u : EuclideanSpace ℝ (Fin 2)) (h : u ∈ U), ∀ (t : ℝ), t • u ∈ U → u ∈ U ∧ t = 1 := sorry

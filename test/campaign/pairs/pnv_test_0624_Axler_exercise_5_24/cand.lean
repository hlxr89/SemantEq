import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy (V : Type*) [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ (c : ℝ) (v : V), T v = c • v → c = 0 ∨ v = 0) (W : Submodule ℝ V) (hW : ∀ (v : V), v ∈ W → T v ∈ W) : Even (finrank ℝ W) := sorry

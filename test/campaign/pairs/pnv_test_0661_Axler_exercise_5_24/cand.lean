import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] (T : End ℝ V) (hT : ∀ (v : V) (μ : ℝ), ¬(T v = μ • v)) {W : Submodule ℝ V} (hW : ∀ w ∈ W, T w ∈ W) : (finrank ℝ W) % 2 = 0 := sorry

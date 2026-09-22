import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type u_1} [AddCommGroup V] [Module ℂ V] {T : Module.End ℂ V} (hT : ∀ (W : Submodule ℂ V), finrank ℂ W = finrank ℂ V - 1 → ∀ (v : V), v ∈ W → T v ∈ W) : ∃ (c : ℂ), ∀ (v : V), T v = c • v := sorry

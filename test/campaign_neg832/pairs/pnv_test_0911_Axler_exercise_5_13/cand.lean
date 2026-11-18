import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : V →ₗ[ℝ] V} (h : ∀ (W : Submodule ℝ V), W < (⊤ : Submodule ℝ V) → LinearMap.range T ≤ W → LinearMap.range T ≤ W.map T) : ∃ a : ℝ, T = a • LinearMap.id := sorry

import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, T '' (U i).carrier ⊆ (U i).carrier) : T '' (Submodule.span ℝ (⋃ i, (U i).carrier)) ⊆ (Submodule.span ℝ (⋃ i, (U i).carrier)) := sorry

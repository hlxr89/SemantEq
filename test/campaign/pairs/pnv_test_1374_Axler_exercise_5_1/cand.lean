import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] {T : V →ₗ[ℝ] V} {m : ℕ} {U : Fin m → Submodule ℝ V} (hU : ∀ i, Submodule.map T (U i) ≤ U i) : Submodule.map T (⨆ i, U i) ≤ ⨆ i, U i := sorry

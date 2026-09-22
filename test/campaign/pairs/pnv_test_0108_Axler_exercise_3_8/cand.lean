import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] (T : V →ₗ[K] W) : ∃ (U : Submodule K V), U ⊓ LinearMap.ker T = ⊥ ∧ LinearMap.range T = ⊤ := sorry

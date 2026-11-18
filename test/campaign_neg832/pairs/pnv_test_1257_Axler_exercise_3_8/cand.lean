import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] (T : V →ₗ[K] W) : ∃ U : Submodule K V, (∀ u₁ u₂ : U, T u₁ = T u₂ → u₁ = u₂) ∧ (∀ w : W, ∃ v : U, T v = w) := sorry

import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {R : Type _} {M : Type _} [Ring R] [AddCommGroup M] [Module R M] (L₁ L₂ : Submodule R M) : L₁ ⊔ L₂ = L₁ ∨ L₁ ⊔ L₂ = L₂ ↔ L₁ ≤ L₂ ∨ L₂ ≤ L₁ := sorry

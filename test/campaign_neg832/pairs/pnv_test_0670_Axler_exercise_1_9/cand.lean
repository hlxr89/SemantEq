import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {U V₁ V₂ : Submodule K V} : U ⊔ V₁ = V₂ ↔ V₁ ≤ U ∨ V₂ ≤ U := sorry

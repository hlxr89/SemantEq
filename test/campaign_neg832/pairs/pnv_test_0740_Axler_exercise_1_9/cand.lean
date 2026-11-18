import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {s t u : Submodule K V} : (s ⊔ t : Submodule K V) = u ↔ s ≤ u ∧ t ≤ u := sorry

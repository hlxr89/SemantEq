import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [AddCommGroup V] [Module ℝ V] (U W : Submodule ℝ V) : (U ⊔ W : Set V) = (U : Set V) ∪ (W : Set V) ↔ U ≤ W ∨ W ≤ U := sorry

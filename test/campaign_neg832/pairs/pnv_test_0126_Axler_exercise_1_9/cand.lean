import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [AddCommGroup V] [Module ℂ V] {W X Y : Subspace ℂ V} (hW : W + Y = ⊤) : W ≤ Y ∨ Y ≤ W := sorry

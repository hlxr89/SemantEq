import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {s t : Set V} (h : t ⊆ Submodule.span K s) : Submodule.span K (s ∪ t) = Submodule.span K s := sorry

import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y} {D : Set X} (hD : Dense D) (h : ∀ p ∈ D, g p = f p) : Continuous g ↔ Continuous f := sorry

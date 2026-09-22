import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y} {E : Set X} (hf : Continuous f) (hg : Continuous g) (hE : Dense E) (he : ∀ p ∈ E, g p = f p) : ∀ p, g p = f p := sorry

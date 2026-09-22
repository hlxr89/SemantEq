import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (Y : Type*) [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y] {X : Type*} [TopologicalSpace X] [Preorder X] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) : Continuous (λ x => min (f x) (g x)) := sorry

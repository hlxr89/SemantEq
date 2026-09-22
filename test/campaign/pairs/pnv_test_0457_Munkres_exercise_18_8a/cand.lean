import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y] {X : Type*} [TopologicalSpace X] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) : IsClosed {x | f x ≤ g x} := sorry

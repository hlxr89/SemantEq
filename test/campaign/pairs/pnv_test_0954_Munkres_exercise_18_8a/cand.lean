import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LinearOrder Y] [OrderTopology Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) : IsClosed {x : X | f x ≤ g x} := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [LinearOrder Y] (f g : X → Y) (hf : Continuous f) (hg : Continuous g) : IsClosed {x : X | f x ≤ g x} := sorry

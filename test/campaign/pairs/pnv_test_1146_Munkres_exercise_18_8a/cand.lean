import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) [Preorder Y] [LocallyFiniteOrder Y] : IsClosed {x : X | f x ≤ g x} := sorry

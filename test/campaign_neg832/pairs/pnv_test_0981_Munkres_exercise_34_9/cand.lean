import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] [T2Space X] {X1 X2 : Set X} (hX1 : IsClosed X1) (hX2 : IsClosed X2) (h1 : MetrizableSpace X1) (h2 : MetrizableSpace X2) (hX : X1 ∪ X2 = Set.univ) : MetrizableSpace X := sorry

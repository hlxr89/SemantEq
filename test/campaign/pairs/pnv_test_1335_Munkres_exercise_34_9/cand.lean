import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {X1 X2 : Set X} (hX1 : IsClosed X1) (hX2 : IsClosed X2) (hX : X = X1 ∪ X2) (hX1_met : MetrizableSpace X1) (hX2_met : MetrizableSpace X2) : MetrizableSpace X := sorry

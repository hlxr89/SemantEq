import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MetrizableSpace X] (X₁ X₂ : Set X) (h₁ : IsClosed X₁) (h₂ : IsClosed X₂) (hX : X = X₁ ∪ X₂) : MetrizableSpace X := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {X₁ X₂ : Set X} (hX₁ : IsClosed X₁) (hX₂ : IsClosed X₂) (h : X = X₁ ∪ X₂) (h₁ : MetrizableSpace X₁) (h₂ : MetrizableSpace X₂) : MetrizableSpace X := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] (hX : ∃ (X₁ X₂ : Set X), IsClosed X₁ ∧ IsClosed X₂ ∧ X₁ ∪ X₂ = X ∧ MetrizableSpace X₁ ∧ MetrizableSpace X₂) : MetrizableSpace X := sorry

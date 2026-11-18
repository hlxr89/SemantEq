import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (𝒯 : Set (TopologicalSpace X)) : (⋃ (𝒯 : Set (TopologicalSpace X)), 𝒯) ≠ { ⊤ } := sorry

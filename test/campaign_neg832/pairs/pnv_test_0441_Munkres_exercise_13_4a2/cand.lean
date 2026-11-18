import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (S : Set (TopologicalSpace X)) (hS : ∀ (α : TopologicalSpace X), α ∈ S) : ∃ (T : TopologicalSpace X), T ∉ S := sorry

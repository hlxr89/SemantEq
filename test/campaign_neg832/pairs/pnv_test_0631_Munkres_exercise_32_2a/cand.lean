import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy (X : β → Type*) [∀ s, TopologicalSpace (X s)] [∀ s, CompactSpace (X s)] [∀ s, T1Space (X s)] [∀ s, Nonempty (X s)] [CompactSpace (∀ s, X s)] [T1Space (∀ s, X s)] : ∀ (s : β), T1Space (X s) := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] (h : ∀ i, Nonempty (X i)) (hX : ∀ i, T2Space (X i)) (h'X : T2Space (∀ i, X i)) : ∀ i, T2Space (X i) := sorry

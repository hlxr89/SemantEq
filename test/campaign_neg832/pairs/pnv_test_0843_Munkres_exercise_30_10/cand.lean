import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (hX : ∀ i, SeparableSpace (X i)) (s : ∀ i, Countable (X i)) : ∃ t : Set (∀ i, X i), Countable t ∧ Dense t := sorry

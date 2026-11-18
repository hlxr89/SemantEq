import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, Countable (X i)] (hX : ∀ i, ∃ D : Set (X i), Dense D) : ∃ D : Set (∀ i, X i), Dense D := sorry

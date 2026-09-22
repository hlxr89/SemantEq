import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ D : Set (X i), Countable D ∧ Dense D) : ∃ D : Set (Π i, X i), Countable D ∧ Dense D := sorry

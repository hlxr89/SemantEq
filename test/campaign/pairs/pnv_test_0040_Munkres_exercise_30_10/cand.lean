import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ D : Set (X i), D.Countable ∧ Dense D) : ∃ D : Set (∀ i, X i), D.Countable ∧ Dense D := sorry

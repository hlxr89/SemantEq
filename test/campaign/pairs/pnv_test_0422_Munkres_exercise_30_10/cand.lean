import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : ∀ i, ∃ S : Set (X i), S.Countable ∧ Dense S) : ∃ S : Set (∀ i, X i), S.Countable ∧ Dense S := sorry

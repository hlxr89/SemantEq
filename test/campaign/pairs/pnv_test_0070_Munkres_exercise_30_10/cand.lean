import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {ι : Type*} [Countable ι] {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (h : ∀ i, ∃ S : Set (π i), S.Countable ∧ Dense S) : ∃ S : Set (∀ i, π i), S.Countable ∧ Dense S := sorry

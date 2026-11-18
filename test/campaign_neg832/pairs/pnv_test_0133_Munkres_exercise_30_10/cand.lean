import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} [Fintype ι] {X : ι → Type*} [Nonempty ι] [∀ i, TopologicalSpace (X i)] (hX : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) : ∃ (s : Set (∀ i, X i)), Countable s ∧ Dense s := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} {ι : Type*} (T : ι → Filter X) : ∃ (T' : Filter X), (∀ α : ι, T α ≤ T') ∧ ∀ (S : Filter X), (∀ α : ι, S ≤ T α) → S ≤ T' := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ α, t ≤ T α) ∧ (∀ t', (∀ α, t' ≤ T α) → t' ≤ t) := sorry

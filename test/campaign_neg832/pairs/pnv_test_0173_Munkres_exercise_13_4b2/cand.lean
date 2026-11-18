import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ (∀ T', (∀ α, T' ≤ T α) → T' ≤ T₀) := sorry

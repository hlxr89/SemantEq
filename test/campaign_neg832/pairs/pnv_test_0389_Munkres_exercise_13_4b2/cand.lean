import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [TopologicalSpace X] {α : Type*} (Ta : α → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ (a : α), τ ≤ Ta a) ∧ ∀ τ' : TopologicalSpace X, (∀ (a : α), τ' ≤ Ta a) → τ ≤ τ' := sorry

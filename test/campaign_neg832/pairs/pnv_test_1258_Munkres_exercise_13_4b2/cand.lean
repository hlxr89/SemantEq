import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} {I : Type*} (T : I → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ i : I, τ ≤ T i) ∧ (∀ τ' : TopologicalSpace X, (∀ i : I, τ' ≤ T i) → τ' ≤ τ) := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [T1Space X] : (∀ {ι : Type*} [Countable ι] {U : ι → Set X}, (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ → ∃ (x : X), ∀ (i : ι), x ∈ U i) ↔ (∀ (S : Set X), (∀ x ∈ S, S ∈ (𝓝 x).sets) → S ∈ {S | IsCompact S}) := sorry

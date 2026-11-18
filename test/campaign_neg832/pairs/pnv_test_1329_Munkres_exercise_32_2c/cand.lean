import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] [∀ i, Nonempty (π i)] (h : NormalSpace (∀ i, π i)) : ∀ i, NormalSpace (π i) := sorry

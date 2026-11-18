import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] (hne : ∀ i, Nonempty (X i)) (h : NormalSpace (∀ i, X i)) : ∀ i, NormalSpace (X i) := sorry

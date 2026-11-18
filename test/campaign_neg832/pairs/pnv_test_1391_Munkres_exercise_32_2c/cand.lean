import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {I : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, NormalSpace (X i)] (hne : ∀ i, Nonempty (X i)) : NormalSpace (∀ i, X i) := sorry

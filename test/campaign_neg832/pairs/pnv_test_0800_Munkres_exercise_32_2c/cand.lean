import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [tX : ∀ i, TopologicalSpace (X i)] (h : ∀ i j, NormalSpace (X i ⊕ X j)) (h' : ∀ i, Nonempty (X i)) : NormalSpace (∀ i, X i) := sorry

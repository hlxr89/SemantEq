import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : NormalSpace (Π i, X i)) (i : ι) : NormalSpace (X i) := sorry

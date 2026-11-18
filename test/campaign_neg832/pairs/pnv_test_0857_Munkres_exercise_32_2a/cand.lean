import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : T2Space (Π i, X i)) (i : ι) : T2Space (X i) := sorry

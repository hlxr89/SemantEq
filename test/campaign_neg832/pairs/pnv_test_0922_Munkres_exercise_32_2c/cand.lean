import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h : NormalSpace (Π i, X i)) (i : ι) [Nonempty (X i)] : NormalSpace (X i) := sorry

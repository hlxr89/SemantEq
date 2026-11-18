import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (hX : NormalSpace (∀ i, π i)) (i : ι) [Nonempty (π i)] : NormalSpace (π i) := sorry

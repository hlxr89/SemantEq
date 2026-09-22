import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, IsConnected (A i)) {U : Set X} (hU : IsConnected U) (h : ∀ i, (A i ∩ U).Nonempty) : IsConnected (U ∪ ⋃ i, A i) := sorry

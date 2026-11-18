import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {A : Set X} (hA : IsConnected A) {ι : Type*} {Ai : ι → Set X} (hAi : ∀ i, IsConnected (Ai i)) (hU : ∀ i, (Ai i ∩ A).Nonempty) : IsConnected (A ∪ ⋃ i, Ai i) := sorry

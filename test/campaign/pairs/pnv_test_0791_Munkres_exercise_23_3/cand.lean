import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsConnected A) {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsConnected (U i)) (hA₁ : ∀ i, (A ∩ U i).Nonempty) : IsConnected (A ∪ ⋃ i, U i) := sorry

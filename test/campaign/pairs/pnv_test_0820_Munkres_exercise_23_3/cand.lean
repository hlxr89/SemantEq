import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsConnected A) {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsConnected (s i)) (h : ∀ i, (s i ∩ A).Nonempty) : IsConnected (A ∪ ⋃ i, s i) := sorry

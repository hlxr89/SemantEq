import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] (A : Set X) (B : ι → Set X) (hA : IsConnected A) (hB : ∀ i, IsConnected (B i)) (h : ∀ i, (B i) ∩ A ≠ ∅) : IsConnected (A ∪ (⋃ i, B i)) := sorry

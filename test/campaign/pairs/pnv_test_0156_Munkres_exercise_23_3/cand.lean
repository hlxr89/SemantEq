import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] (A : Set X) (B : ι → Set X) (hA : IsConnected A) (hB : ∀ (i : ι), IsConnected (B i)) (hB_inter_A : ∀ (i : ι), (B i) ∩ A ≠ ∅) : IsConnected (A ∪ ⋃ (i : ι), B i) := sorry

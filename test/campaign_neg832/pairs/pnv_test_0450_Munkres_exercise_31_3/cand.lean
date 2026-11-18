import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [PartialOrder X] [TopologicalSpace X] [OrderTopology X] : ∀ (x : X) (s : Set X), IsOpen s → x ∈ s → ∃ (t : Set X), IsOpen t ∧ x ∈ t ∧ Disjoint t s := sorry

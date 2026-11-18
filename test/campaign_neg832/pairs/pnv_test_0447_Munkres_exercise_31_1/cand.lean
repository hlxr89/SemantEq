import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [T2Space X] (x y : X) : ∃ (U : Set X) (H : x ∈ U) (V : Set X) (H : y ∈ V), IsClosed U ∧ IsClosed V ∧ Disjoint U V := sorry

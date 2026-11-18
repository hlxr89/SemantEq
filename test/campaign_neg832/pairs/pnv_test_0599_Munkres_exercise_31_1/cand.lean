import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [RegularSpace X] (x y : X) : ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ IsClosed (closure U) ∧ IsClosed (closure V) ∧ Disjoint (closure U) (closure V) := sorry

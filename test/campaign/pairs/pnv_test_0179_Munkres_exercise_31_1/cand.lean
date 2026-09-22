import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [TopologicalSpace X] [RegularSpace X] {x y : X} (h : x ≠ y) : ∃ (u : Set X) (v : Set X), IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint (closure u) (closure v) := sorry

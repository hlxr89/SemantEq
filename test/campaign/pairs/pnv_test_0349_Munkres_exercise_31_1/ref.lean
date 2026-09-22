import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem exercise_31_1 {X : Type*} [TopologicalSpace X]
  (hX : RegularSpace X) (x y : X) (hxy : x ≠ y) :
  ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := sorry

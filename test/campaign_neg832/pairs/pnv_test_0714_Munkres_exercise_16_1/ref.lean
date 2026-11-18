import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem exercise_16_1 {X : Type*} [TopologicalSpace X]
  (Y : Set X)
  (A : Set Y) :
  ∀ U : Set A, IsOpen U ↔ IsOpen (Subtype.val '' U) := sorry

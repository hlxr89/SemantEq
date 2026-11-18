import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f : X → Y} {A : Set X} (h : UniformContinuousOn f A) : ∃ g : X → Y, UniformContinuous g ∧ EqOn f g A ∧ EqOn f g (closure A) := sorry

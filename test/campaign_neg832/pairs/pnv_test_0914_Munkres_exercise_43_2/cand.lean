import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {A : Set X} {f : X → Y} (hfc : UniformContinuousOn f A) : ∃! g : X → Y, Continuous g ∧ EqOn f g A ∧ UniformContinuous g := sorry

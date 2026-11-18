import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (f : X → Y) (A : Set X) (hA : IsClosed A) (hf : UniformContinuousOn f A) : ∃! g : X → Y, ∀ x ∈ A, g x = f x ∧ Continuous g ∧ UniformContinuous g := sorry

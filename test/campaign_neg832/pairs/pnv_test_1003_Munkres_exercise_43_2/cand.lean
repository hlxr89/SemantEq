import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) (A : Set X) (f : X → Y) (hf : UniformContinuousOn f A) : ∃ g : X → Y, ContinuousOn g (closure A) ∧ ∀ x ∈ A, g x = f x ∧ UniformContinuousOn g (closure A) := sorry

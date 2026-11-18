import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [MetricSpace X] [MetricSpace Y] (hY : CompleteSpace Y) (A : Set X) (f : A → Y) (hf : UniformContinuous f) : ∃ g : closure A → Y, Continuous g ∧ UniformContinuous g := sorry

import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [MetricSpace X] [CompactSpace X] [Nonempty X] (f : X → X) (hf : Continuous f) : ∃ x : X, f x = x := sorry

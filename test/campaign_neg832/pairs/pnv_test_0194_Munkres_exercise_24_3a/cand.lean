import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [MetricSpace X] [CompactSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X → X) (hf : Continuous f) (hX : X = Icc 0 1) : ∃ x : X, f x = x := sorry
